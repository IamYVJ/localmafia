/********************************************************************
 * Local Mafia — Game Logic
 * ---------------------------------------------------------------
 * Architecture:
 *   Host  → manages authoritative game state; broadcasts snapshots
 *   Client → sends actions (night ability / vote) to Host via PeerJS
 *
 * Message protocol (Host ↔ Client):
 *
 *   Client → Host
 *     { t:"join",  name, v }
 *     { t:"night", action, targetId | null }
 *     { t:"vote",  targetId | null }
 *     { t:"ping",  ts }
 *
 *   Host → Client
 *     { t:"joined",       roomCode, youId }
 *     { t:"state",        state }                  ← public snapshot
 *     { t:"private_role", role }                   ← private to each player
 *     { t:"investigation",targetName, result }     ← private to Police only
 *     { t:"toast",        msg }
 ********************************************************************/

"use strict";

/* ═══════════════════════════════════════════
   DOM helpers
   ═══════════════════════════════════════════ */
const $ = (sel) => document.querySelector(sel);

/** Tiny element factory */
function el(tag, attrs = {}, children = []) {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") n.className = v;
    else if (k === "text") n.textContent = v;
    else if (k.startsWith("on") && typeof v === "function") n.addEventListener(k.slice(2), v);
    else n.setAttribute(k, v);
  }
  for (const c of children) n.appendChild(c);
  return n;
}

/* ═══════════════════════════════════════════
   SPA view switching
   ═══════════════════════════════════════════ */
const views = {
  home:  $("#viewHome"),
  lobby: $("#viewLobby"),
  game:  $("#viewGame"),
};

function showView(name) {
  for (const [k, node] of Object.entries(views)) {
    node.classList.toggle("active", k === name);
  }
  if (name === "home") resetHomePanels();
}

/** Home landing: collapse the host/join forms back to the two CTAs. */
function resetHomePanels() {
  const choose = $("#ctaChoose"), host = $("#panelHost"), join = $("#panelJoin");
  if (choose) choose.hidden = false;
  if (host)   host.hidden   = true;
  if (join)   join.hidden   = true;
}

/* ═══════════════════════════════════════════
   Theme
   Night (dark) is default. During a game the
   phase automatically drives the theme.
   ═══════════════════════════════════════════ */
let manualTheme = "dark";

function setTheme(theme) {
  document.body.setAttribute("data-theme", theme);
  const isLight = theme === "light";
  $("#themeIcon").textContent  = isLight ? "☀️" : "🌙";
  $("#themeLabel").textContent = isLight ? "Day"  : "Night";
}

let themePhase = null;

function applyPhaseTheme(phase) {
  // Only auto-drive the theme when the phase actually changes, so a manual
  // toggle made mid-phase isn't immediately undone by the next state render.
  if (phase === themePhase) return;
  themePhase = phase;
  if (phase === "night") setTheme("dark");
  else if (["day", "vote", "ended"].includes(phase)) setTheme("light");
  else setTheme(manualTheme);
}

$("#btnTheme").addEventListener("click", () => {
  manualTheme = document.body.getAttribute("data-theme") === "dark" ? "light" : "dark";
  setTheme(manualTheme);
  toast("Theme set to " + (manualTheme === "dark" ? "Night" : "Day"));
});

/* ═══════════════════════════════════════════
   Toast notifications
   ═══════════════════════════════════════════ */
let toastTimer = null;

function toast(msg, ms = 2400) {
  const t = $("#toast");
  t.textContent = msg;
  t.classList.add("show");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove("show"), ms);
}

/* ═══════════════════════════════════════════
   App state
   ═══════════════════════════════════════════ */
const APP_VERSION = "1.0";

let peer       = null;   // PeerJS Peer instance
let isHost     = false;
let roomCode   = null;

let myId       = null;   // this device's PeerJS ID
let myName     = "";
let myRole     = null;   // delivered privately by Host
let myPoliceMemo = "";   // latest private investigation result
let myMafiaTeam  = [];   // names of fellow Mafia (Mafia only)
let myVigilanteShots = null; // bullets remaining (Vigilante only)

/** Host-only: map peerId → DataConnection */
const conns = new Map();

/** Client-only: DataConnection to the Host */
let hostConn = null;

/** Last received public game state (used for rendering) */
let publicState = null;

/** Host-only: full authoritative game state */
let hostState = null;

/* ═══════════════════════════════════════════
   Utilities
   ═══════════════════════════════════════════ */

/** Room-code alphabet — confusable chars (O/I/0/1) intentionally excluded */
const CODE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";

/** 4-char room code */
function randCode4() {
  return Array.from({length: 4}, () => CODE_ALPHABET[Math.floor(Math.random() * CODE_ALPHABET.length)]).join("");
}

function sanitizeName(raw) {
  let n = (raw || "").trim().replace(/\s+/g, " ");
  if (!n) n = "Player";
  return n.slice(0, 18);
}

function nowTime() {
  return new Date().toLocaleTimeString([], {hour: "2-digit", minute: "2-digit"});
}

function roleIcon(role) {
  return ({
    Mafia:"🔫", Dentist:"🦷", Angel:"😇", Police:"👮",
    Mayor:"🎩", Vigilante:"🎯", Jester:"🃏", Citizen:"🧑",
  })[role] ?? "🎭";
}

function roleDesc(role) {
  return ({
    Mafia:     "At night, choose someone to kill.",
    Dentist:   "At night, choose someone to silence (they can't vote tomorrow).",
    Angel:     "At night, protect someone (prevents a night kill).",
    Police:    "At night, investigate someone (you learn Mafia or Innocent).",
    Mayor:     "Town leader. Your vote counts twice during the day.",
    Vigilante: "One bullet for the whole game — shoot someone at night.",
    Jester:    "You win if the town votes to execute you.",
    Citizen:   "No night action. Watch, discuss, vote."
  })[role] ?? "—";
}

/** Faction a role belongs to (used for win checks). Jester is neutral. */
function roleTeam(role) {
  if (role === "Mafia")  return "Mafia";
  if (role === "Jester") return "Neutral";
  return "Town";
}

function clampPhase(phase) { return phase || "lobby"; }

/* ═══════════════════════════════════════════
   Host: authoritative state factory
   ═══════════════════════════════════════════ */
function newHostState(hostId, hostName) {
  return {
    roomCode: hostId,
    phase: "lobby",   // lobby | night | day | vote | ended
    day: 0,
    log: [{ts: nowTime(), kind: "muted", text: "Room created. Waiting for players…"}],
    players: {
      [hostId]: {
        id: hostId, name: hostName, isHost: true,
        connected: true, alive: true, role: null, silencedForDay: null,
      }
    },
    night: buildEmptyNight(),
    vote:  buildEmptyVote(),
    winner: null,   // "Mafia" | "Town" | "Jester"
    settings: {
      autoCloseVote: false,  // close the vote once everyone has voted
    },
  };
}

function buildEmptyNight() {
  return {mafia:{}, dentist:{}, angel:{}, police:{}, vigilante:{}, resolved:false, lastResult:null};
}
function buildEmptyVote() {
  return {votes:{}, resolved:false, lastResult:null};
}

/**
 * Append a line to the game log.
 * `secret` entries are bookkeeping that could reveal roles (e.g. which player
 * acted at night). They are kept host-side for debugging but are stripped from
 * every public snapshot, so no player — not even the host — sees them in the
 * narrator.
 */
function hostAddLog(kind, text, secret = false) {
  hostState.log.push({ts: nowTime(), kind, text, secret});
  if (hostState.log.length > 120) hostState.log.splice(0, hostState.log.length - 120);
}

/* ── Alive/role queries ── */
function hostAliveIds() {
  return Object.values(hostState.players).filter(p => p.alive).map(p => p.id);
}
function hostMafiaAliveIds() {
  return Object.values(hostState.players).filter(p => p.alive && p.role === "Mafia").map(p => p.id);
}
function hostTownAliveIds() {
  return Object.values(hostState.players).filter(p => p.alive && p.role !== "Mafia").map(p => p.id);
}
function hostIsSilencedToday(player) {
  return !!(player.silencedForDay && player.silencedForDay === hostState.day);
}
function hostEligibleVoters() {
  return Object.values(hostState.players)
    .filter(p => p.alive && !hostIsSilencedToday(p))
    .map(p => p.id);
}
/** Vote weight by role — the Mayor's vote counts double. */
function hostVoteWeight(playerId) {
  return hostState.players[playerId]?.role === "Mayor" ? 2 : 1;
}
/** Total ballot weight across all eligible voters (used for the majority threshold). */
function hostEligibleWeight() {
  return hostEligibleVoters().reduce((sum, id) => sum + hostVoteWeight(id), 0);
}
function hostComputeWin() {
  const mafia = hostMafiaAliveIds().length;
  const town  = hostTownAliveIds().length;
  if (mafia === 0)       return "Town";
  if (mafia >= town)     return "Mafia";
  return null;
}

/* ═══════════════════════════════════════════
   Host: public snapshot builder
   Roles are never sent in the public snapshot —
   only private_role messages reveal them.
   ═══════════════════════════════════════════ */
function buildPublicSnapshotFor(peerId) {
  const ps = {
    roomCode: hostState.roomCode,
    phase: hostState.phase,
    day: hostState.day,
    winner: hostState.winner,
    log: hostState.log.filter(l => !l.secret).slice(-10),
    players: [],
    voteTallies: null,
    you: {id: peerId},
  };

  for (const p of Object.values(hostState.players)) {
    ps.players.push({
      id: p.id, name: p.name, isHost: !!p.isHost,
      connected: !!p.connected, alive: !!p.alive,
      silenced: (p.silencedForDay === hostState.day) && p.alive,
    });
  }

  if (hostState.phase === "vote") {
    const tallies = {};
    for (const [voterId, target] of Object.entries(hostState.vote.votes)) {
      if (!target) continue;
      tallies[target] = (tallies[target] || 0) + hostVoteWeight(voterId);
    }
    const totalWeight = hostEligibleWeight();
    ps.voteTallies = {
      eligible: totalWeight,
      majority: Math.floor(totalWeight / 2) + 1,
      tallies,
    };
  }

  return ps;
}

function hostBroadcastState() {
  // Host renders its own UI first…
  publicState = buildPublicSnapshotFor(hostState.roomCode);
  renderAll();
  // …then sends personalised snapshots to each connected client.
  for (const [pid, conn] of conns.entries()) {
    if (conn && conn.open) {
      conn.send({t: "state", state: buildPublicSnapshotFor(pid)});
    }
  }
  updateHostLobbyControls();
}

/* ── Role delivery ── */
function hostSendPrivateRole(playerId) {
  const p = hostState.players[playerId];
  if (!p) return;

  if (playerId === hostState.roomCode) {
    // Host is this device
    myRole = p.role;
    myVigilanteShots = p.vigilanteShots;
    $("#roleCard").style.display = "flex";
    renderRoleCard();
    return;
  }

  const conn = conns.get(playerId);
  if (conn && conn.open) conn.send({t: "private_role", role: p.role, shots: p.vigilanteShots});
}

/** Refresh a player's private extras (e.g. remaining bullets) without re-toasting their role. */
function hostSendRoleInfo(playerId) {
  const p = hostState.players[playerId];
  if (!p) return;
  if (playerId === hostState.roomCode) { myVigilanteShots = p.vigilanteShots; return; }
  const conn = conns.get(playerId);
  if (conn && conn.open) conn.send({t: "role_info", shots: p.vigilanteShots});
}

function hostSendInvestigation(policeId, targetId) {
  const police = hostState.players[policeId];
  const target = hostState.players[targetId];
  if (!police || !target || !police.alive) return;

  const result = target.role === "Mafia" ? "Mafia" : "Innocent";

  if (policeId === hostState.roomCode) {
    myPoliceMemo = `${target.name} is ${result}.`;
    hostAddLog("muted", `👮 Investigation delivered privately to ${police.name}.`, true);
    return;
  }

  const conn = conns.get(policeId);
  if (conn && conn.open) conn.send({t: "investigation", targetName: target.name, result});
  hostAddLog("muted", `👮 Investigation delivered privately to ${police.name}.`, true);
}

/* ═══════════════════════════════════════════
   Host: role assignment
   ═══════════════════════════════════════════ */
function hostAssignRoles() {
  const ids = Object.keys(hostState.players);
  const n   = ids.length;

  // Roles unlock progressively as the table grows (max 10 players).
  const mafiaCount    = n >= 7 ? 2 : 1;
  const wantPolice    = n >= 4;
  const wantAngel     = n >= 5;
  const wantDentist   = n >= 6;
  const wantMayor     = n >= 8;
  const wantVigilante = n >= 9;
  const wantJester    = n >= 10;

  const deck = [];
  for (let i = 0; i < mafiaCount; i++) deck.push("Mafia");
  if (wantPolice)    deck.push("Police");
  if (wantAngel)     deck.push("Angel");
  if (wantDentist)   deck.push("Dentist");
  if (wantMayor)     deck.push("Mayor");
  if (wantVigilante) deck.push("Vigilante");
  if (wantJester)    deck.push("Jester");
  while (deck.length < n) deck.push("Citizen");

  shuffle(ids);
  shuffle(deck);

  for (let i = 0; i < n; i++) {
    const p = hostState.players[ids[i]];
    p.role = deck[i];
    // Vigilante gets a single bullet for the whole game.
    p.vigilanteShots = (p.role === "Vigilante") ? 1 : null;
  }

  hostAddLog("ok", "Roles assigned. Night falls.");
  for (const id of ids) hostSendPrivateRole(id);
  hostSendMafiaTeams();
}

/* Tell each Mafia who their fellow Mafia are (if any). */
function hostSendMafiaTeams() {
  const mafiaIds = Object.values(hostState.players)
    .filter(p => p.role === "Mafia")
    .map(p => p.id);

  for (const id of mafiaIds) {
    const names = mafiaIds
      .filter(other => other !== id)
      .map(other => hostState.players[other].name);

    if (id === hostState.roomCode) {
      myMafiaTeam = names;
      continue;
    }
    const conn = conns.get(id);
    if (conn && conn.open) conn.send({t: "mafia_team", names});
  }
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

/* ═══════════════════════════════════════════
   Host: phase transitions
   ═══════════════════════════════════════════ */
function hostStartGame() {
  if (hostState.phase !== "lobby") return;
  if (Object.keys(hostState.players).length < 4) {
    hostAddLog("muted", "Need at least 4 players to start.");
    hostBroadcastState();
    return;
  }
  hostAssignRoles();
  hostState.phase = "night";
  hostState.night = buildEmptyNight();
  hostBroadcastState();
}

function hostStartVoting() {
  if (hostState.phase !== "day") return;
  hostState.phase = "vote";
  hostState.vote  = buildEmptyVote();
  hostAddLog("muted", "Voting begins. Choose carefully.");
  hostBroadcastState();
}

function hostNextNight() {
  if (hostState.phase !== "day") return;
  const win = hostComputeWin();
  if (win) { return hostEndGame(win); }
  hostState.phase = "night";
  hostState.night = buildEmptyNight();
  hostAddLog("muted", "Night falls. Roles, act in secret.");
  hostBroadcastState();
}

function hostEndGame(win) {
  hostState.phase  = "ended";
  hostState.winner = win;
  hostAddLog(win === "Town" ? "ok" : "danger", `Game over: ${win} wins.`);
  hostBroadcastState();
}

/**
 * Return the finished room to the lobby with the same connected players.
 * Roles, deaths and per-round state are wiped so the host can adjust the
 * roster (people leave/join) and start a fresh game. Players who already
 * disconnected are dropped.
 */
function hostReturnToLobby() {
  if (hostState.phase !== "ended") return;

  for (const id of Object.keys(hostState.players)) {
    const p = hostState.players[id];
    if (!p.connected && !p.isHost) { delete hostState.players[id]; continue; }
    p.role           = null;
    p.silencedForDay = null;
    p.alive          = true;
    p.vigilanteShots = null;
  }

  hostState.phase  = "lobby";
  hostState.day    = 0;
  hostState.winner = null;
  hostState.night  = buildEmptyNight();
  hostState.vote   = buildEmptyVote();
  hostState.log    = [{ts: nowTime(), kind: "muted",
    text: "Back in the lobby. Players can leave or join, then the Host starts again."}];

  hostBroadcastState();
}

function hostExecutePlayer(playerId, reasonText) {
  const p = hostState.players[playerId];
  if (!p || !p.alive) return;
  p.alive = false;
  hostAddLog("danger", reasonText);
}

/* ── Vote resolution ── */
function hostResolveVote(force = false) {
  if (hostState.phase !== "vote") return;

  // Tally weighted votes (Mayor counts double); majority is of the total weight.
  const majority = Math.floor(hostEligibleWeight() / 2) + 1;
  const tally    = {};

  for (const voterId of hostEligibleVoters()) {
    const t = hostState.vote.votes[voterId] || null;
    if (!t) continue;
    if (!hostState.players[t]?.alive) continue;
    tally[t] = (tally[t] || 0) + hostVoteWeight(voterId);

    // Auto-execute on majority (unless we're just force-resolving)
    if (!force && tally[t] >= majority) {
      hostExecutePlayer(t, `🗳️ Majority vote. ${hostState.players[t].name} was executed.`);
      hostState.vote.resolved = true;
      hostState.vote.lastResult = {executedId: t, tie: false};
      hostAfterExecution(t);
      return;
    }
  }

  // Auto-resolve pass only checks for a majority; if none yet, keep collecting.
  if (!force) { hostBroadcastState(); return; }

  // Forced resolution — pick highest, handle ties
  let bestId = null, bestCount = 0, tie = false;
  for (const [id, c] of Object.entries(tally)) {
    if (c > bestCount)      { bestId = id; bestCount = c; tie = false; }
    else if (c === bestCount) tie = true;
  }

  if (!bestId || bestCount === 0 || tie) {
    hostAddLog("muted", "No execution today.");
    hostState.vote.resolved    = true;
    hostState.vote.lastResult  = {executedId: null, tie: true};
    hostAfterExecution(null);
    return;
  }

  hostExecutePlayer(bestId, `🗳️ ${hostState.players[bestId].name} was executed by vote.`);
  hostState.vote.resolved   = true;
  hostState.vote.lastResult = {executedId: bestId, tie: false};
  hostAfterExecution(bestId);
}

/**
 * After a day execution: a Jester voted out wins immediately and ends the game;
 * otherwise check the normal win conditions and advance to the next day.
 */
function hostAfterExecution(executedId) {
  if (executedId && hostState.players[executedId]?.role === "Jester") {
    hostAddLog("ok", `🃏 ${hostState.players[executedId].name} was the Jester — and wanted to be voted out. Jester wins!`);
    hostEndGame("Jester");
    return;
  }
  hostAfterVoteAdvance();
}

function hostAfterVoteAdvance() {
  const win = hostComputeWin();
  if (win) { hostEndGame(win); return; }
  hostState.phase = "day";
  hostAddLog("muted", "Day ends. Prepare for night.");
  hostBroadcastState();
}

/* ── Night action collection ── */
function hostHandleNightAction(fromId, action, targetId) {
  if (hostState.phase !== "night") return;
  const actor  = hostState.players[fromId];
  if (!actor || !actor.alive) return;
  if (targetId !== null && !hostState.players[targetId]?.alive) return;

  const valid = {
    mafia_kill:          {role:"Mafia",     bag:"mafia"},
    dentist_silence:     {role:"Dentist",   bag:"dentist"},
    angel_protect:       {role:"Angel",     bag:"angel"},
    police_investigate:  {role:"Police",    bag:"police"},
    vigilante_shoot:     {role:"Vigilante", bag:"vigilante"},
  }[action];

  if (!valid || actor.role !== valid.role) return;

  // Vigilante can only fire if they still have a bullet (skipping is always allowed).
  if (action === "vigilante_shoot" && targetId !== null && (actor.vigilanteShots || 0) <= 0) return;

  hostState.night[valid.bag][fromId] = targetId;
  hostAddLog("muted", `${roleIcon(actor.role)} Action received (${actor.name}).`, true);

  if (action === "police_investigate" && targetId) {
    hostSendInvestigation(fromId, targetId);
  }

  hostBroadcastState();
  hostMaybeResolveNight();
}

function hostMaybeResolveNight(force = false) {
  if (hostState.phase !== "night") return;
  if (hostState.night.resolved) return;

  const alive = Object.values(hostState.players).filter(p => p.alive);
  if (!alive.some(p => p.role)) return;

  if (!force) {
    const byRole = (role) => alive.filter(p => p.role === role).map(p => p.id);
    const allIn  = (ids, bag) => ids.every(id => Object.hasOwn(bag, id));
    // Only wait on a Vigilante who still has a bullet — out-of-ammo ones have no action.
    const armedVigilantes = alive
      .filter(p => p.role === "Vigilante" && (p.vigilanteShots || 0) > 0)
      .map(p => p.id);

    if (!allIn(byRole("Mafia"),   hostState.night.mafia))     return;
    if (!allIn(byRole("Dentist"), hostState.night.dentist))   return;
    if (!allIn(byRole("Angel"),   hostState.night.angel))     return;
    if (!allIn(byRole("Police"),  hostState.night.police))    return;
    if (!allIn(armedVigilantes,   hostState.night.vigilante)) return;
  } else {
    hostAddLog("muted", "Host resolved the night early.");
  }

  hostState.night.resolved = true;

  const mafiaTarget     = pluralityPick(Object.values(hostState.night.mafia).filter(Boolean));
  const angelTarget     = firstNonNull(Object.values(hostState.night.angel));
  const silenceTarget   = firstNonNull(Object.values(hostState.night.dentist));
  const vigilanteTarget = firstNonNull(Object.values(hostState.night.vigilante));

  if (silenceTarget && hostState.players[silenceTarget]) {
    hostState.players[silenceTarget].silencedForDay = hostState.day + 1;
  }

  // Spend the Vigilante's bullet if they actually fired.
  for (const [vigId, tgt] of Object.entries(hostState.night.vigilante)) {
    if (tgt && hostState.players[vigId]) {
      hostState.players[vigId].vigilanteShots = Math.max(0, (hostState.players[vigId].vigilanteShots || 0) - 1);
      hostSendRoleInfo(vigId);
    }
  }

  // An Angel's protection blocks any single night attack on that target.
  const attacked = new Set();
  if (mafiaTarget)     attacked.add(mafiaTarget);
  if (vigilanteTarget) attacked.add(vigilanteTarget);
  const blocked = !!(angelTarget && attacked.has(angelTarget));
  if (angelTarget) attacked.delete(angelTarget);

  const killedIds = [...attacked].filter(id => hostState.players[id]?.alive);
  for (const id of killedIds) hostState.players[id].alive = false;

  // Announce results
  hostState.day += 1;
  hostState.phase = "day";

  if (killedIds.length) {
    for (const id of killedIds) {
      hostAddLog("danger", `☠️ ${hostState.players[id].name} was found dead at dawn.`);
    }
  } else if (blocked) {
    hostAddLog("ok", "😇 Someone was attacked, but an Angel protected them.");
  } else {
    hostAddLog("muted", "Dawn arrives. No one died tonight.");
  }

  if (blocked && killedIds.length) {
    hostAddLog("ok", "😇 An Angel thwarted another attack in the night.");
  }

  if (silenceTarget && hostState.players[silenceTarget]) {
    hostAddLog("muted", `🦷 ${hostState.players[silenceTarget].name} is silenced today (can't vote).`);
  }

  const win = hostComputeWin();
  if (win) { hostEndGame(win); return; }

  hostBroadcastState();
}

function hostHandleVote(fromId, targetId) {
  if (hostState.phase !== "vote") return;
  const voter = hostState.players[fromId];
  if (!voter || !voter.alive || hostIsSilencedToday(voter)) return;
  if (targetId === fromId) return; // can't vote for yourself
  if (targetId !== null && !hostState.players[targetId]?.alive) return;

  hostState.vote.votes[fromId] = targetId;
  hostAddLog("muted", `🗳️ Vote received (${voter.name}).`, true);
  hostBroadcastState();
  hostResolveVote(false); // check for auto majority

  // Optional: if the host enabled it, close voting as soon as every eligible
  // player has cast a vote (or abstained) — even without a majority.
  if (hostState.phase === "vote" && hostState.settings?.autoCloseVote) {
    const eligible = hostEligibleVoters();
    const allVoted = eligible.length > 0
      && eligible.every(id => Object.hasOwn(hostState.vote.votes, id));
    if (allVoted) {
      hostAddLog("muted", "Everyone has voted — closing the vote.");
      hostResolveVote(true);
    }
  }
}

/* ─ small helpers ─ */
function pluralityPick(arr) {
  if (!arr.length) return null;
  const count = {};
  for (const x of arr) count[x] = (count[x] || 0) + 1;
  let best = null, bestC = 0, tie = false;
  for (const [id, c] of Object.entries(count)) {
    if (c > bestC)      { best = id; bestC = c; tie = false; }
    else if (c === bestC) tie = true;
  }
  return tie ? null : best;
}
function firstNonNull(arr) {
  for (const x of arr) if (x) return x;
  return null;
}

/* ═══════════════════════════════════════════
   PeerJS: Host — handle incoming connections
   ═══════════════════════════════════════════ */
function hostOnIncomingConnection(conn) {
  conn.on("open", () => {
    conns.set(conn.peer, conn);
  });

  conn.on("data", (msg) => {
    if (!msg || typeof msg !== "object") return;

    if (msg.t === "join") {
      const name = sanitizeName(msg.name);
      const existing = hostState.players[conn.peer];

      hostState.players[conn.peer] = {
        id: conn.peer, name, isHost: false,
        connected: true, alive: existing?.alive ?? true,
        role: existing?.role ?? null,
        silencedForDay: existing?.silencedForDay ?? null,
        vigilanteShots: existing?.vigilanteShots ?? null,
      };

      // Late joiner after game started → spectator (no role, not alive)
      const isLateJoiner = hostState.phase !== "lobby" && !hostState.players[conn.peer].role;
      if (isLateJoiner) {
        hostState.players[conn.peer].alive = false;
      }

      conn.send({t: "joined", roomCode: hostState.roomCode, youId: conn.peer});
      hostAddLog("ok", `${name} joined.`);
      hostBroadcastState();

      if (isLateJoiner) {
        conn.send({t: "toast", msg: "Game already in progress — you joined as a spectator."});
      }

      // Resend private info if rejoining mid-game
      if (hostState.phase !== "lobby" && hostState.players[conn.peer].role) {
        hostSendPrivateRole(conn.peer);
        if (hostState.players[conn.peer].role === "Mafia") hostSendMafiaTeams();
      }
    }

    if (msg.t === "night") hostHandleNightAction(conn.peer, msg.action, msg.targetId ?? null);
    if (msg.t === "vote")  hostHandleVote(conn.peer, msg.targetId ?? null);
  });

  conn.on("close", () => {
    const p = hostState.players[conn.peer];
    if (p) {
      p.connected = false;
      if (hostState.phase !== "lobby" && p.alive) {
        p.alive = false;
        hostAddLog("danger", `⚡ ${p.name} disconnected and is out.`);
      } else {
        hostAddLog("muted", `${p.name} left.`);
      }
    }
    conns.delete(conn.peer);
    hostBroadcastState();
  });

  conn.on("error", () => { /* non-fatal; remaining peers continue */ });
}

/* ═══════════════════════════════════════════
   PeerJS: Client — connect to host
   ═══════════════════════════════════════════ */
function clientConnectToHost(code) {
  return new Promise((resolve, reject) => {
    hostConn = peer.connect(code, {
      reliable: true,
      serialization: "json",
      metadata: {v: APP_VERSION},
    });

    hostConn.on("open", () => {
      $("#netStatus").textContent = "Connected";
      hostConn.send({t: "join", name: myName, v: APP_VERSION});
      resolve();
    });

    hostConn.on("data", (msg) => {
      if (!msg || typeof msg !== "object") return;

      if (msg.t === "joined") {
        roomCode = msg.roomCode;
        $("#roomCode").textContent = roomCode;
      }
      if (msg.t === "state") {
        publicState = msg.state;
        renderAll();
      }
      if (msg.t === "private_role") {
        myRole = msg.role;
        myVigilanteShots = msg.shots ?? null;
        $("#roleCard").style.display = "flex";
        renderRoleCard();
        toast(`Your role: ${myRole} ${roleIcon(myRole)}`);
      }
      if (msg.t === "role_info") {
        myVigilanteShots = msg.shots ?? null;
        renderAll();
      }
      if (msg.t === "mafia_team") {
        myMafiaTeam = Array.isArray(msg.names) ? msg.names : [];
        renderAll();
      }
      if (msg.t === "investigation") {
        myPoliceMemo = `${msg.targetName} is ${msg.result}.`;
        toast("Investigation result received (private).");
        renderAll();
      }
      if (msg.t === "toast") {
        toast(msg.msg);
      }
    });

    hostConn.on("close", () => {
      $("#netStatus").textContent = "Disconnected";
      toast("Connection to Host closed.");
      cleanupAll();
      showView("home");
      setTheme(manualTheme);
    });

    hostConn.on("error", reject);
  });
}

/* ═══════════════════════════════════════════
   PeerJS: create Peer instance
   ═══════════════════════════════════════════ */
function createPeerWithId(idOrNull) {
  return new Promise((resolve, reject) => {
    try {
      peer = idOrNull ? new Peer(idOrNull) : new Peer();
    } catch(e) {
      reject(e); return;
    }

    peer.on("open", (id) => { myId = id; resolve(id); });

    // Only the Host accepts inbound connections
    peer.on("connection", (conn) => {
      if (isHost) hostOnIncomingConnection(conn);
      else conn.close();
    });

    peer.on("disconnected", () => { $("#netStatus").textContent = "Peer disconnected"; });
    peer.on("close",        () => { $("#netStatus").textContent = "Peer closed"; });
    peer.on("error", reject);
  });
}

/* ═══════════════════════════════════════════
   Rendering
   ═══════════════════════════════════════════ */
let lastRenderedPhase = null;

function renderAll() {
  if (!publicState) return;
  const phase = clampPhase(publicState.phase);

  // A fresh night wipes any stale private investigation result.
  if (phase === "night" && lastRenderedPhase !== "night") myPoliceMemo = "";
  lastRenderedPhase = phase;

  applyPhaseTheme(phase);

  if (phase === "lobby") {
    // Returning to the lobby (new game with same players) — clear any role
    // state left over from the previous round so nothing leaks or lingers.
    myRole = null;
    myPoliceMemo = "";
    myMafiaTeam = [];
    myVigilanteShots = null;
    $("#roleCard").style.display = "none";
    showView("lobby");
    renderLobby();
  } else {
    showView("game");
    renderGame();
  }
}

function renderLobby() {
  $("#roomCode").textContent  = roomCode || "----";
  $("#netStatus").textContent = isHost ? "Hosting" : "Connected";

  const wrap = $("#lobbyPlayers");
  wrap.innerHTML = "";

  const players = (publicState?.players || [])
    .slice()
    .sort((a, b) => (b.isHost - a.isHost) || a.name.localeCompare(b.name));

  for (const p of players) {
    const badges = el("div", {class: "badges"});
    if (p.isHost)   badges.appendChild(el("span", {class:"badge host", text:"Host"}));
    badges.appendChild(el("span", {class:`badge ${p.alive ? "alive":"dead"}`, text: p.alive ? "Alive":"Dead"}));
    if (p.id === myId) badges.appendChild(el("span", {class:"badge me", text:"You"}));
    if (!p.connected)  badges.appendChild(el("span", {class:"badge",    text:"Offline"}));

    wrap.appendChild(el("div", {class:"item"}, [
      el("div", {class:"who"}, [
        el("div", {class:"name", text: p.name}),
        el("div", {class:"meta", text: p.id === myId ? "This is you" : (p.isHost ? "Host device" : "Guest")}),
      ]),
      badges,
    ]));
  }

  $("#lobbyHint").textContent = isHost
    ? "Start when everyone has joined. Minimum 4 players recommended."
    : "Wait for the Host to start the game.";

  updateHostLobbyControls();
}

function updateHostLobbyControls() {
  const settings = $("#lobbySettings");
  if (!isHost) {
    $("#btnStartGame").style.display = "none";
    if (settings) settings.hidden = true;
    return;
  }
  $("#btnStartGame").style.display = "inline-flex";
  const count = Object.keys(hostState.players).length;
  $("#btnStartGame").disabled = !(hostState.phase === "lobby" && count >= 4);

  if (settings) {
    settings.hidden = false;
    $("#optAutoClose").checked = !!hostState.settings?.autoCloseVote;
  }
}

function renderRoleCard() {
  const role = myRole || "—";
  $("#roleIcon").textContent = roleIcon(role);
  $("#roleName").textContent = role;
  $("#roleDesc").textContent = roleDesc(role);

  const me    = publicState?.players?.find(p => p.id === myId);
  const alive = !!me?.alive;
  $("#badgeAlive").textContent = alive ? "Alive" : "Dead";
  $("#badgeAlive").className   = "badge " + (alive ? "alive" : "dead");
}

function renderNarrator() {
  const box = $("#narrator");
  box.innerHTML = "";
  const lines = publicState?.log || [];
  if (!lines.length) { box.appendChild(el("div", {class:"line muted", text:"—"})); return; }
  for (const ln of lines) {
    box.appendChild(el("div", {class:`line ${ln.kind || "muted"}`, text:`[${ln.ts}] ${ln.text}`}));
  }
}

function renderPlayersListGame() {
  const wrap    = $("#gamePlayers");
  wrap.innerHTML = "";
  const players = (publicState?.players || [])
    .slice()
    .sort((a,b) => (b.alive - a.alive) || (b.isHost - a.isHost) || a.name.localeCompare(b.name));

  const tallies = publicState?.voteTallies?.tallies || {};
  const phase   = publicState?.phase;

  for (const p of players) {
    const badges = el("div", {class:"badges"});
    if (p.isHost)   badges.appendChild(el("span", {class:"badge host",  text:"Host"}));
    if (p.id === myId) badges.appendChild(el("span", {class:"badge me", text:"You"}));
    badges.appendChild(el("span", {class:`badge ${p.alive ? "alive":"dead"}`, text: p.alive ? "Alive":"Dead"}));
    if (p.silenced)  badges.appendChild(el("span", {class:"badge silenced", text:"Silenced"}));
    if (!p.connected) badges.appendChild(el("span", {class:"badge",         text:"Offline"}));
    if (phase === "vote" && p.alive) {
      const c = tallies[p.id] || 0;
      badges.appendChild(el("span", {class:"badge", text:`Votes: ${c}`}));
    }

    wrap.appendChild(el("div", {class:"item"}, [
      el("div", {class:"who"}, [
        el("div", {class:"name", text: p.name}),
        el("div", {class:"meta", text: p.id === myId ? "You" : (p.isHost ? "Host" : "Player")}),
      ]),
      badges,
    ]));
  }
}

function renderGame() {
  const phase = clampPhase(publicState?.phase);
  const day   = publicState?.day || 0;

  $("#phaseTitle").textContent = {
    night: `Night ${day + 1}`,
    day:   `Day ${day}`,
    vote:  `Vote (Day ${day})`,
    ended: "Game Over",
  }[phase] ?? "—";

  $("#phaseSub").textContent = {
    night: "Roles act in secret.",
    day:   "Discuss what happened.",
    vote:  "Majority vote executes a suspect.",
    ended: publicState?.winner ? `${publicState.winner} wins.` : "—",
  }[phase] ?? "—";

  $("#roleCard").style.display = myRole ? "flex" : "none";
  if (myRole) renderRoleCard();

  renderNarrator();
  renderActionArea();
  renderPlayersListGame();

  $("#hostControls").style.display = isHost ? "flex" : "none";
  if (isHost) {
    $("#btnHostResolveNight").disabled = hostState.phase !== "night";
    $("#btnHostToVote").disabled       = hostState.phase !== "day";
    $("#btnHostResolveVote").disabled  = hostState.phase !== "vote";
    $("#btnHostNextNight").disabled    = hostState.phase !== "day";
    $("#btnHostPlayAgain").disabled    = hostState.phase !== "ended";
  }

  const me       = publicState?.players?.find(p => p.id === myId);
  const silenced = !!me?.silenced;
  if (phase === "vote" && silenced) {
    $("#gameHint").textContent = "You are silenced today: you cannot vote.";
  } else if (phase === "night" && myRole === "Citizen" && me?.alive) {
    $("#gameHint").textContent = "You have no night action. Watch for patterns, then vote by day.";
  } else if (phase === "ended") {
    $("#gameHint").textContent = "Tap Leave to return home and host/join a new room.";
  } else {
    $("#gameHint").textContent = "";
  }
}

function renderActionArea() {
  const area  = $("#actionArea");
  area.innerHTML = "";

  const phase   = clampPhase(publicState?.phase);
  const players = publicState?.players || [];
  const me      = players.find(p => p.id === myId);
  const alive   = !!me?.alive;

  if (!alive) {
    const spectator = !myRole && phase !== "ended";
    area.appendChild(el("div", {class:"hint", text: spectator
      ? "You're spectating — the game was already in progress when you joined. You'll be dealt in next game."
      : "You are dead. You can still watch the game state."}));
    return;
  }

  if (myRole === "Mafia" && myMafiaTeam.length) {
    area.appendChild(el("div", {class:"chip"}, [
      el("span", {text:"🔫"}),
      el("span", {text: `Your Mafia: ${myMafiaTeam.join(", ")}`}),
    ]));
  }

  if (myPoliceMemo) {
    area.appendChild(el("div", {class:"chip"}, [
      el("span", {text:"👮"}),
      el("span", {text: myPoliceMemo}),
    ]));
  }

  if (phase === "night") {
    const role = myRole || "Citizen";
    if (role === "Citizen") {
      area.appendChild(el("div", {class:"hint", text:"Night: Citizens sleep. (No action)"}));
      return;
    }

    if (role === "Mayor") {
      area.appendChild(el("div", {class:"hint", text:"Night: the Mayor sleeps. Your power is your double vote by day."}));
      return;
    }

    const specMap = {
      Mafia:     {action:"mafia_kill",         title:"Choose a target to kill",       note:"Only the Mafia kills at night.", canSelf:false},
      Dentist:   {action:"dentist_silence",     title:"Choose a target to silence",    note:"Silenced players can't vote tomorrow.", canSelf:false},
      Angel:     {action:"angel_protect",       title:"Choose someone to protect",     note:"Protection prevents a night kill.", canSelf:true},
      Police:    {action:"police_investigate",  title:"Choose someone to investigate", note:"You'll learn Mafia or Innocent (private).", canSelf:false},
      Vigilante: {action:"vigilante_shoot",     title:"Choose someone to shoot",       note:"One bullet for the whole game. Choose wisely — or Skip.", canSelf:false},
    };

    const spec = specMap[role];
    if (!spec) {
      area.appendChild(el("div", {class:"hint", text:"No night action available."}));
      return;
    }

    // Vigilante with no bullets left can only sit out the night.
    if (role === "Vigilante" && (myVigilanteShots || 0) <= 0) {
      area.appendChild(el("div", {class:"chip"}, [
        el("span", {text:"🎯"}),
        el("span", {text:"Out of bullets — your shot's been spent."}),
      ]));
      area.appendChild(el("div", {class:"hint", text:"Nothing to do tonight. Sit tight and watch."}));
      return;
    }

    area.appendChild(el("div", {class:"chip"}, [
      el("span", {text: roleIcon(role)}),
      el("span", {text: spec.title}),
    ]));
    area.appendChild(el("div", {class:"hint", text: spec.note}));

    const grid = el("div", {class:"grid"});
    for (const p of players) {
      if (!p.alive) continue;
      if (!spec.canSelf && p.id === myId) continue;
      const btn = el("button", {class:"btn", onclick: () => submitNight(spec.action, p.id)});
      btn.textContent = p.name;
      grid.appendChild(btn);
    }

    const skip = el("button", {class:"btn ghost", onclick: () => submitNight(spec.action, null)});
    skip.textContent = "Skip";

    area.appendChild(el("div", {class:"targets"}, [
      el("div", {class:"grid"}, [grid]),
      el("div", {class:"row"},  [skip]),
    ]));
    return;
  }

  if (phase === "day") {
    area.appendChild(el("div", {class:"hint", text:"Day: Discuss in person, then the Host starts voting."}));
    return;
  }

  if (phase === "vote") {
    const silenced = !!me?.silenced;
    if (silenced) {
      area.appendChild(el("div", {class:"chip"}, [
        el("span", {text:"🦷"}),
        el("span", {text:"You are silenced today. Voting disabled."}),
      ]));
      return;
    }

    const vt = publicState?.voteTallies;
    if (vt) {
      area.appendChild(el("div", {class:"chip"}, [
        el("span", {text:"🗳️"}),
        el("span", {text:`Majority: ${vt.majority} of ${vt.eligible}`}),
      ]));
    }
    if (myRole === "Mayor") {
      area.appendChild(el("div", {class:"chip"}, [
        el("span", {text:"🎩"}),
        el("span", {text:"As Mayor, your vote counts twice."}),
      ]));
    }
    area.appendChild(el("div", {class:"hint", text:"Vote to execute a suspect. Majority executes immediately."}));

    const grid = el("div", {class:"grid"});
    for (const p of players) {
      if (!p.alive) continue;
      if (p.id === myId) continue; // can't vote for yourself
      const btn = el("button", {class:"btn", onclick: () => submitVote(p.id)});
      btn.textContent = p.name;
      grid.appendChild(btn);
    }
    const abstain = el("button", {class:"btn ghost", onclick: () => submitVote(null)});
    abstain.textContent = "Abstain";

    area.appendChild(el("div", {class:"targets"}, [
      el("div", {class:"grid"}, [grid]),
      el("div", {class:"row"},  [abstain]),
    ]));
    return;
  }

  if (phase === "ended") {
    area.appendChild(el("div", {class:"hint", text:"Game over."}));
  }
}

/* ═══════════════════════════════════════════
   Submit actions
   ═══════════════════════════════════════════ */
function submitNight(action, targetId) {
  if (!publicState || publicState.phase !== "night") return;
  if (isHost) {
    hostHandleNightAction(myId, action, targetId);
    toast("Night action submitted.");
  } else if (hostConn?.open) {
    hostConn.send({t:"night", action, targetId});
    toast("Night action sent.");
  }
}

function submitVote(targetId) {
  if (!publicState || publicState.phase !== "vote") return;
  if (isHost) {
    hostHandleVote(myId, targetId);
    toast("Vote submitted.");
  } else if (hostConn?.open) {
    hostConn.send({t:"vote", targetId});
    toast("Vote sent.");
  }
}

/* ═══════════════════════════════════════════
   Button handlers: Home
   ═══════════════════════════════════════════ */

/* Progressive disclosure: reveal the relevant form, hide the CTAs. */
$("#btnShowHost").addEventListener("click", () => {
  $("#ctaChoose").hidden = true;
  $("#panelHost").hidden = false;
  $("#inpName").focus();
});
$("#btnShowJoin").addEventListener("click", () => {
  $("#ctaChoose").hidden = true;
  $("#panelJoin").hidden = false;
  $("#inpJoinName").focus();
});
document.querySelectorAll("[data-back]").forEach(b => b.addEventListener("click", resetHomePanels));

/* Enter submits from the relevant input. */
$("#inpName").addEventListener("keydown", (e) => { if (e.key === "Enter") $("#btnHost").click(); });
$("#inpRoom").addEventListener("keydown", (e) => { if (e.key === "Enter") $("#btnJoin").click(); });
$("#inpJoinName").addEventListener("keydown", (e) => { if (e.key === "Enter") $("#inpRoom").focus(); });

$("#btnHost").addEventListener("click", async () => {
  myName = sanitizeName($("#inpName").value);
  isHost = true;
  myRole = null;
  myPoliceMemo = "";
  $("#netStatus").textContent = "Creating…";
  toast("Creating room…");

  for (let attempt = 0; attempt < 12; attempt++) {
    const code = randCode4();
    try {
      await createPeerWithId(code);
      roomCode = code;
      break;
    } catch(err) {
      try { peer && peer.destroy(); } catch(_) {}
      peer = null;
      if (err?.type !== "unavailable-id") {
        toast("Peer error: " + (err?.type || err?.message || "unknown"));
        isHost = false;
        return;
      }
    }
  }

  if (!roomCode) {
    toast("Could not find an available room code. Try again.");
    isHost = false;
    return;
  }

  hostState  = newHostState(roomCode, myName);
  publicState = buildPublicSnapshotFor(roomCode);
  $("#roomCode").textContent  = roomCode;
  $("#netStatus").textContent = "Hosting";
  showView("lobby");
  renderLobby();
  toast("Room created: " + roomCode);
});

$("#btnJoin").addEventListener("click", async () => {
  myName   = sanitizeName($("#inpJoinName").value);
  roomCode = ($("#inpRoom").value || "").trim().toUpperCase().slice(0, 4);

  if (roomCode.length !== 4) { toast("Enter a 4-character room code."); return; }
  if ([...roomCode].some(ch => !CODE_ALPHABET.includes(ch))) {
    toast("Invalid code. Room codes don't use O, I, 0 or 1.");
    return;
  }

  isHost = false;
  myRole = null;
  myPoliceMemo = "";
  publicState  = {phase:"lobby", players:[]};
  $("#roomCode").textContent  = roomCode;
  $("#netStatus").textContent = "Connecting…";
  showView("lobby");
  renderLobby();

  try {
    await createPeerWithId(null);
  } catch(err) {
    toast("Peer error: " + (err?.type || err?.message || "unknown"));
    cleanupAll(); showView("home"); setTheme(manualTheme);
    return;
  }

  try {
    await clientConnectToHost(roomCode);
    toast("Joined room " + roomCode);
  } catch(err) {
    toast("Could not connect to Host. Check code and try again.");
    cleanupAll(); showView("home"); setTheme(manualTheme);
  }
});

/* ═══════════════════════════════════════════
   Button handlers: Lobby & Game
   ═══════════════════════════════════════════ */
$("#btnCopyCode").addEventListener("click", async () => {
  if (!roomCode) return;
  try {
    await navigator.clipboard.writeText(roomCode);
    toast("Room code copied.");
  } catch(_) {
    toast("Copy failed. Share manually: " + roomCode);
  }
});

$("#btnLeaveLobby").addEventListener("click", ()  => { cleanupAll(); showView("home"); setTheme(manualTheme); });
$("#btnLeaveGame").addEventListener("click",  ()  => { cleanupAll(); showView("home"); setTheme(manualTheme); });
$("#btnStartGame").addEventListener("click",  ()  => { if (isHost) hostStartGame(); });

$("#btnHostResolveNight").addEventListener("click", () => { if (isHost) hostMaybeResolveNight(true); });
$("#btnHostToVote").addEventListener("click",      () => { if (isHost) hostStartVoting(); });
$("#btnHostResolveVote").addEventListener("click", () => { if (isHost) hostResolveVote(true); });
$("#btnHostNextNight").addEventListener("click",   () => { if (isHost) hostNextNight(); });
$("#btnHostPlayAgain").addEventListener("click",   () => { if (isHost) hostReturnToLobby(); });

/* Host-only lobby setting: auto-close voting once everyone has voted. */
$("#optAutoClose").addEventListener("change", (e) => {
  if (!isHost || !hostState) return;
  hostState.settings.autoCloseVote = e.target.checked;
  toast(e.target.checked
    ? "Voting will auto-close once everyone votes."
    : "Auto-close voting disabled.");
});

/* ═══════════════════════════════════════════
   Cleanup / leave
   ═══════════════════════════════════════════ */
function cleanupAll() {
  try { hostConn?.close(); } catch(_) {}
  hostConn = null;

  for (const [, c] of conns.entries()) { try { c.close(); } catch(_) {} }
  conns.clear();

  try { if (peer && !peer.destroyed) peer.destroy(); } catch(_) {}
  peer = null;

  isHost = false; roomCode = null; myId = null;
  myRole = null; myPoliceMemo = ""; myMafiaTeam = []; myVigilanteShots = null;
  publicState = null; hostState = null;
  lastRenderedPhase = null; themePhase = null;

  $("#netStatus").textContent  = "Idle";
  $("#roomCode").textContent   = "----";
  $("#roleCard").style.display = "none";
  ["narrator","lobbyPlayers","gamePlayers","actionArea"].forEach(id => { $("#"+id).innerHTML = ""; });
  $("#hostControls").style.display = "none";
}

/* ── Boot ── */
setTheme("dark");
