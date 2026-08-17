import { useCallback, useEffect, useRef, useState } from "react";
import "./App.css";

const MIN_SIZE = 7;
const MAX_SIZE = 19;

const POPULATION_SIZE = 500;
const MUTATION_CHANCE = 0.05;
const MUTATION_AMOUNT = 0.10;

const PASS = -1;
const KOMI_SMALL = 3.5;
const KOMI_LARGE = 6.5;

const STORAGE_KEY = "evolutionary-go-v1";

/*
  Genome parameters.

  Evolution changes these numbers.
  The code determines WHAT the creature can observe;
  evolution determines how important each observation is.
*/
const P = {
  BIAS: 0,

  CAPTURE: 1,
  CAPTURE_SIZE: 2,

  SAVE_ATARI: 3,
  ATTACK_ATARI: 4,

  LIBERTIES: 5,
  SELF_ATARI: 6,

  CONNECT: 7,
  CUT: 8,

  ADJACENT_OWN: 9,
  ADJACENT_ENEMY: 10,
  ADJACENT_EMPTY: 11,

  OWN_TERRITORY: 12,
  ENEMY_TERRITORY: 13,
  CONTESTED: 14,

  FILL_EYE: 15,

  EDGE: 16,
  SECOND_LINE: 17,
  CENTER: 18,

  CAPTURE_DANGER: 19,
  CAPTURE_DANGER_SIZE: 20,

  REMOVE_LIBERTIES: 21,
  HELP_WEAK_GROUP: 22,

  PHASE: 23,

  PASS: 24,
  PASS_SETTLED: 25,
  PASS_CONTESTED: 26,

  REGION_SIZE: 27,
};

const PARAM_COUNT = 28;

function other(player) {
  return -player;
}

function indexOf(x, y, size) {
  return y * size + x;
}

function neighbors(index, size) {
  const x = index % size;
  const y = Math.floor(index / size);

  const result = [];

  if (x > 0) result.push(index - 1);
  if (x + 1 < size) result.push(index + 1);
  if (y > 0) result.push(index - size);
  if (y + 1 < size) result.push(index + size);

  return result;
}

function sameBoard(a, b) {
  if (!a || !b) return false;
  if (a.length !== b.length) return false;

  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return false;
  }

  return true;
}

function findGroup(board, start, size) {
  const color = board[start];

  if (color === 0) {
    return {
      stones: [],
      liberties: new Set(),
    };
  }

  const seen = new Uint8Array(board.length);
  const stack = [start];

  const stones = [];
  const liberties = new Set();
  let representative = start;

  while (stack.length > 0) {
    const point = stack.pop();

    if (seen[point]) continue;
    seen[point] = 1;

    if (board[point] !== color) continue;

    stones.push(point);

    if (point < representative) {
      representative = point;
    }

    for (const next of neighbors(point, size)) {
      if (board[next] === 0) {
        liberties.add(next);
      } else if (
        board[next] === color &&
        !seen[next]
      ) {
        stack.push(next);
      }
    }
  }

  return {
    stones,
    liberties,
    representative,
  };
}

/*
  Build group lookup once per move instead of
  flood-filling the same groups for every candidate.
*/
function buildGroupCache(board, size) {
  const seen = new Uint8Array(
    board.length
  );

  const pointGroup =
    new Int16Array(board.length);

  pointGroup.fill(-1);

  const groups = [];

  for (
    let i = 0;
    i < board.length;
    i++
  ) {
    if (
      board[i] === 0 ||
      seen[i]
    ) {
      continue;
    }

    const group = findGroup(
      board,
      i,
      size
    );

    const id = groups.length;

    group.id = id;

    groups.push(group);

    for (const stone of group.stones) {
      seen[stone] = 1;
      pointGroup[stone] = id;
    }
  }

  return {
    pointGroup,
    groups,
  };
}

function createGame(size) {
  return {
    size,

    board: new Int8Array(size * size),

    toPlay: 1,

    passes: 0,
    moveNumber: 0,

    captures: {
      black: 0,
      white: 0,
    },

    /*
      Simple ko.

      This is much faster than copying an entire
      superko history for every candidate move.
    */
    previousBoard: null,
  };
}

/*
  Fast move simulation.

  This performs:
  - occupied-point check
  - captures
  - suicide check
  - simple ko

  It does NOT modify the original state.
*/
function tryMove(state, move) {
  if (move === PASS) {
    return {
      ...state,

      board: state.board.slice(),

      toPlay: other(state.toPlay),

      passes: state.passes + 1,
      moveNumber: state.moveNumber + 1,

      captures: {
        ...state.captures,
      },

      previousBoard: state.board.slice(),
    };
  }

  if (
    move < 0 ||
    move >= state.board.length ||
    state.board[move] !== 0
  ) {
    return null;
  }

  const board = state.board.slice();

  const player = state.toPlay;
  const enemy = other(player);

  board[move] = player;

  let captured = 0;

  const checkedEnemy = new Uint8Array(
    board.length
  );

  for (const next of neighbors(move, state.size)) {
    if (
      board[next] !== enemy ||
      checkedEnemy[next]
    ) {
      continue;
    }

    const group = findGroup(
      board,
      next,
      state.size
    );

    for (const stone of group.stones) {
      checkedEnemy[stone] = 1;
    }

    if (group.liberties.size === 0) {
      captured += group.stones.length;

      for (const stone of group.stones) {
        board[stone] = 0;
      }
    }
  }

  const ownGroup = findGroup(
    board,
    move,
    state.size
  );

  // Suicide.
  if (ownGroup.liberties.size === 0) {
    return null;
  }

  // Simple ko.
  if (
    state.previousBoard &&
    sameBoard(board, state.previousBoard)
  ) {
    return null;
  }

  const captures = {
    ...state.captures,
  };

  if (player === 1) {
    captures.black += captured;
  } else {
    captures.white += captured;
  }

  return {
    ...state,

    board,

    toPlay: enemy,

    passes: 0,
    moveNumber: state.moveNumber + 1,

    captures,

    previousBoard: state.board.slice(),
  };
}

/*
  Territory + captures + komi.

  Stones themselves are NOT points.

  This matches the scoring behavior you wanted,
  rather than area scoring.
*/
function scoreGame(state) {
  const size = state.size;

  const komi =
    size <= 9
      ? KOMI_SMALL
      : KOMI_LARGE;

  const board = state.board;

  const seen = new Uint8Array(
    board.length
  );

  let blackTerritory = 0;
  let whiteTerritory = 0;

  for (let i = 0; i < board.length; i++) {
    if (
      board[i] !== 0 ||
      seen[i]
    ) {
      continue;
    }

    const region = [];
    const borders = new Set();

    const stack = [i];

    seen[i] = 1;

    while (stack.length > 0) {
      const point = stack.pop();

      region.push(point);

      for (const next of neighbors(
        point,
        size
      )) {
        const value = board[next];

        if (value === 0) {
          if (!seen[next]) {
            seen[next] = 1;
            stack.push(next);
          }
        } else {
          borders.add(value);
        }
      }
    }

    if (borders.size === 1) {
      if (borders.has(1)) {
        blackTerritory +=
          region.length;
      } else if (borders.has(-1)) {
        whiteTerritory +=
          region.length;
      }
    }
  }

  const black =
    blackTerritory +
    state.captures.black;

  const white =
    whiteTerritory +
    state.captures.white +
    komi;

  return {
    black,
    white,

    blackTerritory,
    whiteTerritory,

    blackCaptures:
      state.captures.black,

    whiteCaptures:
      state.captures.white,

    komi,

    winner:
      black > white ? 1 : -1,

    margin:
      Math.abs(black - white),
  };
}

/*
  Compute all empty regions ONCE for a position.

  This is much faster than flood-filling the board
  separately for every possible move.
*/
function computeRegionMap(state) {
  const board = state.board;
  const size = state.size;

  const visited = new Uint8Array(
    board.length
  );

  const owner =
    new Int8Array(board.length);

  const regionSize =
    new Uint16Array(board.length);

  const contested =
    new Uint8Array(board.length);

  let totalOwned = 0;
  let totalContested = 0;

  for (let i = 0; i < board.length; i++) {
    if (
      board[i] !== 0 ||
      visited[i]
    ) {
      continue;
    }

    const region = [];
    const borders = new Set();

    const stack = [i];

    visited[i] = 1;

    while (stack.length > 0) {
      const point = stack.pop();

      region.push(point);

      for (const next of neighbors(
        point,
        size
      )) {
        const value = board[next];

        if (value === 0) {
          if (!visited[next]) {
            visited[next] = 1;
            stack.push(next);
          }
        } else {
          borders.add(value);
        }
      }
    }

    let regionOwner = 0;

    if (borders.size === 1) {
      if (borders.has(1)) {
        regionOwner = 1;
      } else if (borders.has(-1)) {
        regionOwner = -1;
      }
    }

    const isContested =
      borders.size !== 1;

    for (const point of region) {
      owner[point] = regionOwner;

      regionSize[point] =
        region.length;

      contested[point] =
        isContested ? 1 : 0;
    }

    if (regionOwner !== 0) {
      totalOwned += region.length;
    } else {
      totalContested +=
        region.length;
    }
  }

  const totalEmpty =
    totalOwned + totalContested;

  return {
    owner,
    regionSize,
    contested,

    totalOwned,
    totalContested,

    settled:
      totalEmpty === 0
        ? 1
        : totalOwned / totalEmpty,
  };
}

function countAdjacentGroups(
  state,
  move,
  color,
  groupCache
) {
  const groups = new Set();

  for (const next of neighbors(
    move,
    state.size
  )) {
    if (
      state.board[next] !== color
    ) {
      continue;
    }

    const id =
      groupCache.pointGroup[next];

    if (id >= 0) {
      groups.add(id);
    }
  }

  return groups.size;
}

function countWeakFriendlyGroupsHelped(
  state,
  move,
  player,
  groupCache
) {
  const seen = new Set();
  let result = 0;

  for (const next of neighbors(
    move,
    state.size
  )) {
    if (
      state.board[next] !== player
    ) {
      continue;
    }

    const id =
      groupCache.pointGroup[next];

    if (id < 0 || seen.has(id)) {
      continue;
    }

    seen.add(id);

    if (
      groupCache.groups[id].liberties
        .size <= 2
    ) {
      result += 1;
    }
  }

  return result;
}

function countEnemyLibertyPressure(
  state,
  move,
  enemy,
  groupCache
) {
  const seen = new Set();

  let pressure = 0;

  for (const next of neighbors(
    move,
    state.size
  )) {
    if (
      state.board[next] !== enemy
    ) {
      continue;
    }

    const id =
      groupCache.pointGroup[next];

    if (id < 0 || seen.has(id)) {
      continue;
    }

    seen.add(id);

    const liberties =
      groupCache.groups[id].liberties
        .size;

    if (liberties === 1) {
      pressure += 4;
    } else if (liberties === 2) {
      pressure += 2;
    } else if (liberties === 3) {
      pressure += 1;
    }
  }

  return pressure;
}

function isSimpleEye(
  state,
  move,
  player
) {
  const ns = neighbors(
    move,
    state.size
  );

  if (ns.length === 0) {
    return false;
  }

  for (const next of ns) {
    if (
      state.board[next] !== player
    ) {
      return false;
    }
  }

  return true;
}

/*
  If the new group has one liberty, test whether
  the opponent can play there and remove it.
*/
function getImmediateCaptureDanger(
  state,
  move,
  nextState
) {
  if (
    move === PASS ||
    !nextState
  ) {
    return {
      dangerous: false,
      size: 0,
    };
  }

  const player = state.toPlay;

  if (
    nextState.board[move] !== player
  ) {
    return {
      dangerous: true,
      size: 1,
    };
  }

  const group = findGroup(
    nextState.board,
    move,
    state.size
  );

  if (group.liberties.size !== 1) {
    return {
      dangerous: false,
      size: 0,
    };
  }

  const liberty =
    group.liberties.values().next().value;

  const reply =
    tryMove(nextState, liberty);

  if (!reply) {
    return {
      dangerous: false,
      size: 0,
    };
  }

  let survivors = 0;

  for (const stone of group.stones) {
    if (
      reply.board[stone] === player
    ) {
      survivors += 1;
    }
  }

  if (survivors === 0) {
    return {
      dangerous: true,
      size: group.stones.length,
    };
  }

  return {
    dangerous: false,
    size: 0,
  };
}

/*
  Generate legal candidate moves once.

  We reuse the already simulated nextState while
  evaluating the move.
*/
function getCandidates(state) {
  const candidates = [];

  for (
    let move = 0;
    move < state.board.length;
    move++
  ) {
    if (
      state.board[move] !== 0
    ) {
      continue;
    }

    const nextState =
      tryMove(state, move);

    if (nextState) {
      candidates.push({
        move,
        nextState,
      });
    }
  }

  candidates.push({
    move: PASS,
    nextState:
      tryMove(state, PASS),
  });

  return candidates;
}

function getMoveFeatures(
  state,
  candidate,
  regions,
  groupCache
) {
  const features =
    new Float64Array(PARAM_COUNT);

  features[P.BIAS] = 1;

  const move = candidate.move;

  const size = state.size;

  const phase = Math.min(
    1,
    state.moveNumber /
      Math.max(
        1,
        size * size * 1.2
      )
  );

  features[P.PHASE] = phase;

  if (move === PASS) {
    features[P.PASS] = 1;

    features[P.PASS_SETTLED] =
      regions.settled;

    features[P.PASS_CONTESTED] =
      regions.totalContested /
      state.board.length;

    return features;
  }

  const player = state.toPlay;
  const enemy = other(player);

  const x = move % size;

  const y =
    Math.floor(move / size);

  const edgeDistance = Math.min(
    x,
    y,
    size - 1 - x,
    size - 1 - y
  );

  const center =
    (size - 1) / 2;

  const centerDistance =
    (
      Math.abs(x - center) +
      Math.abs(y - center)
    ) /
    Math.max(1, size - 1);

  features[P.EDGE] =
    edgeDistance === 0 ? 1 : 0;

  features[P.SECOND_LINE] =
    edgeDistance === 1 ? 1 : 0;

  features[P.CENTER] =
    1 - centerDistance;

  let adjacentOwn = 0;
  let adjacentEnemy = 0;
  let adjacentEmpty = 0;

  for (const next of neighbors(
    move,
    size
  )) {
    const value =
      state.board[next];

    if (value === player) {
      adjacentOwn++;
    } else if (
      value === enemy
    ) {
      adjacentEnemy++;
    } else {
      adjacentEmpty++;
    }
  }

  features[P.ADJACENT_OWN] =
    adjacentOwn / 4;

  features[P.ADJACENT_ENEMY] =
    adjacentEnemy / 4;

  features[P.ADJACENT_EMPTY] =
    adjacentEmpty / 4;

  const ownGroups =
    countAdjacentGroups(
      state,
      move,
      player,
      groupCache
    );

  const enemyGroups =
    countAdjacentGroups(
      state,
      move,
      enemy,
      groupCache
    );

  features[P.CONNECT] =
    Math.min(1, ownGroups / 3);

  features[P.CUT] =
    Math.min(1, enemyGroups / 3);

  const nextState =
    candidate.nextState;

  const captured =
    player === 1
      ? nextState.captures.black -
        state.captures.black
      : nextState.captures.white -
        state.captures.white;

  features[P.CAPTURE] =
    captured > 0 ? 1 : 0;

  features[P.CAPTURE_SIZE] =
    Math.min(
      1,
      captured / 8
    );

  const ownGroup = findGroup(
    nextState.board,
    move,
    size
  );

  const liberties =
    ownGroup.liberties.size;

  features[P.LIBERTIES] =
    Math.min(
      1,
      liberties / 8
    );

  features[P.SELF_ATARI] =
    liberties === 1 ? 1 : 0;

  /*
    Save-atari feature:
    playing beside a friendly group that currently
    has one liberty.
  */
  let savesAtari = 0;

  const seenOwn =
    new Set();

  for (const next of neighbors(
    move,
    size
  )) {
    if (
      state.board[next] !== player
    ) {
      continue;
    }

    const id =
      groupCache.pointGroup[next];

    if (
      id < 0 ||
      seenOwn.has(id)
    ) {
      continue;
    }

    seenOwn.add(id);

    const group =
      groupCache.groups[id];

    if (
      group.liberties.size === 1 &&
      group.liberties.has(move)
    ) {
      savesAtari +=
        group.stones.length;
    }
  }

  features[P.SAVE_ATARI] =
    Math.min(
      1,
      savesAtari / 6
    );

  /*
    Attack-atari feature.
  */
  let attacksAtari = 0;

  const seenEnemy =
    new Set();

  for (const next of neighbors(
    move,
    size
  )) {
    if (
      state.board[next] !== enemy
    ) {
      continue;
    }

    const id =
      groupCache.pointGroup[next];

    if (
      id < 0 ||
      seenEnemy.has(id)
    ) {
      continue;
    }

    seenEnemy.add(id);

    const group =
      groupCache.groups[id];

    if (
      group.liberties.size <= 2
    ) {
      attacksAtari +=
        group.stones.length;
    }
  }

  features[P.ATTACK_ATARI] =
    Math.min(
      1,
      attacksAtari / 6
    );

  features[P.REMOVE_LIBERTIES] =
    Math.min(
      1,
      countEnemyLibertyPressure(
        state,
        move,
        enemy,
        groupCache
      ) / 6
    );

  features[P.HELP_WEAK_GROUP] =
    Math.min(
      1,
      countWeakFriendlyGroupsHelped(
        state,
        move,
        player,
        groupCache
      ) / 3
    );

  /*
    Territory awareness.
  */
  const owner =
    regions.owner[move];

  features[P.OWN_TERRITORY] =
    owner === player ? 1 : 0;

  features[P.ENEMY_TERRITORY] =
    owner === enemy ? 1 : 0;

  features[P.CONTESTED] =
    regions.contested[move]
      ? 1
      : 0;

  features[P.REGION_SIZE] =
    Math.min(
      1,
      regions.regionSize[move] /
        state.board.length
    );

  features[P.FILL_EYE] =
    isSimpleEye(
      state,
      move,
      player
    )
      ? 1
      : 0;

  const danger =
    getImmediateCaptureDanger(
      state,
      move,
      nextState
    );

  features[P.CAPTURE_DANGER] =
    danger.dangerous ? 1 : 0;

  features[P.CAPTURE_DANGER_SIZE] =
    Math.min(
      1,
      danger.size / 8
    );

  return features;
}

function weightedScore(
  genome,
  features
) {
  let score = 0;

  for (
    let i = 0;
    i < PARAM_COUNT;
    i++
  ) {
    score +=
      genome.params[i] *
      features[i];
  }

  return score;
}

/*
  The original creature.

  These values are deliberately only mildly sensible.
  Evolution is expected to change them.

  Every parameter is non-zero so multiplicative
  mutation can affect every parameter.
*/
function createBaseGenome() {
  const params =
    new Float64Array(PARAM_COUNT);

  params[P.BIAS] = 0.01;

  params[P.CAPTURE] = 1.0;
  params[P.CAPTURE_SIZE] = 1.0;

  params[P.SAVE_ATARI] = 0.8;
  params[P.ATTACK_ATARI] = 0.5;

  params[P.LIBERTIES] = 0.3;
  params[P.SELF_ATARI] = -1.0;

  params[P.CONNECT] = 0.2;
  params[P.CUT] = 0.2;

  params[P.ADJACENT_OWN] = 0.05;
  params[P.ADJACENT_ENEMY] = 0.05;
  params[P.ADJACENT_EMPTY] = 0.1;

  params[P.OWN_TERRITORY] = -0.8;
  params[P.ENEMY_TERRITORY] = -0.1;
  params[P.CONTESTED] = 0.2;

  params[P.FILL_EYE] = -0.8;

  params[P.EDGE] = -0.05;
  params[P.SECOND_LINE] = 0.05;
  params[P.CENTER] = 0.05;

  params[P.CAPTURE_DANGER] = -1.0;
  params[P.CAPTURE_DANGER_SIZE] = -1.0;

  params[P.REMOVE_LIBERTIES] = 0.3;
  params[P.HELP_WEAK_GROUP] = 0.5;

  params[P.PHASE] = 0.01;

  params[P.PASS] = -0.4;
  params[P.PASS_SETTLED] = 0.8;
  params[P.PASS_CONTESTED] = -0.8;

  params[P.REGION_SIZE] = 0.01;

  return {
    params,
    birthGeneration: 0,
  };
}

function cloneGenome(genome) {
  return {
    params:
      new Float64Array(
        genome.params
      ),

    birthGeneration:
      genome.birthGeneration,
  };
}

/*
  EXACT evolutionary mutation rule:

  Every copied parameter:
  5% chance of changing.

  If changed:
  multiply by a random number from
  0.9 through 1.1.
*/
function mutatedCopy(
  parent,
  generation
) {
  const child = {
    params:
      new Float64Array(
        parent.params
      ),

    birthGeneration:
      generation,
  };

  for (
    let i = 0;
    i < PARAM_COUNT;
    i++
  ) {
    if (
      Math.random() <
      MUTATION_CHANCE
    ) {
      const factor =
        1 +
        (
          Math.random() * 2 - 1
        ) *
          MUTATION_AMOUNT;

      child.params[i] *=
        factor;
    }
  }

  return child;
}

function createPopulation() {
  const original =
    createBaseGenome();

  const population = [];

  for (
    let i = 0;
    i < POPULATION_SIZE;
    i++
  ) {
    population.push(
      cloneGenome(original)
    );
  }

  return population;
}

function shuffle(array) {
  for (
    let i = array.length - 1;
    i > 0;
    i--
  ) {
    const j =
      Math.floor(
        Math.random() *
          (i + 1)
      );

    const temp = array[i];

    array[i] = array[j];
    array[j] = temp;
  }

  return array;
}

function moveHasFightingValue(
  state,
  candidate
) {
  const move = candidate.move;
  const player = state.toPlay;
  const enemy = other(player);
  const nextState =
    candidate.nextState;

  const captured =
    player === 1
      ? nextState.captures.black -
        state.captures.black
      : nextState.captures.white -
        state.captures.white;

  if (captured > 0) {
    return true;
  }

  for (const next of neighbors(
    move,
    state.size
  )) {
    if (
      state.board[next] === enemy
    ) {
      return true;
    }
  }

  return false;
}

function shouldPass(
  state,
  candidates
) {
  const boardCandidates =
    candidates.filter(
      (candidate) =>
        candidate.move !== PASS
    );

  if (
    boardCandidates.length === 0
  ) {
    return true;
  }

  let stones = 0;

  for (
    let i = 0;
    i < state.board.length;
    i++
  ) {
    if (state.board[i] !== 0) {
      stones++;
    }
  }

  if (
    stones / state.board.length <
    0.55
  ) {
    return false;
  }

  return boardCandidates.every(
    (candidate) =>
      !moveHasFightingValue(
        state,
        candidate
      )
  );
}

/*
  A creature simply picks the legal move
  with the highest parametric score.

  Equal moves are chosen randomly.
*/
function chooseCreatureMove(
  state,
  genome
) {
  const candidates =
    getCandidates(state);

  if (shouldPass(state, candidates)) {
    return candidates.find(
      (candidate) =>
        candidate.move === PASS
    );
  }

  const regions =
    computeRegionMap(state);

  const groupCache =
    buildGroupCache(
      state.board,
      state.size
    );

  let bestScore = -Infinity;
  let bestCandidates = [];

  for (const candidate of candidates) {
    const features =
      getMoveFeatures(
        state,
        candidate,
        regions,
        groupCache
      );

    const score =
      weightedScore(
        genome,
        features
      );

    if (
      score >
      bestScore + 1e-10
    ) {
      bestScore = score;

      bestCandidates = [
        candidate,
      ];
    } else if (
      Math.abs(
        score - bestScore
      ) <= 1e-10
    ) {
      bestCandidates.push(
        candidate
      );
    }
  }

  return bestCandidates[
    Math.floor(
      Math.random() *
        bestCandidates.length
    )
  ];
}

function playEvolutionGame(
  creatureA,
  creatureB,
  size
) {
  /*
    Randomize colors so evolution cannot
    accidentally select for "always being Black".
  */
  let black;
  let white;

  if (Math.random() < 0.5) {
    black = creatureA;
    white = creatureB;
  } else {
    black = creatureB;
    white = creatureA;
  }

  let state =
    createGame(size);

  /*
    Emergency termination.

    Normal games should finish by passing.
    If primitive creatures refuse to pass,
    we eventually score anyway.
  */
  const maxMoves =
    size * size * 1.5;

  while (
    state.passes < 2 &&
    state.moveNumber < maxMoves
  ) {
    const creature =
      state.toPlay === 1
        ? black
        : white;

    const choice =
      chooseCreatureMove(
        state,
        creature
      );

    state =
      choice.nextState;
  }

  const score =
    scoreGame(state);

  const winner =
    score.winner === 1
      ? black
      : white;

  const loser =
    winner === black
      ? white
      : black;

  return {
    winner,
    loser,

    score,

    moves:
      state.moveNumber,

    endedByPass:
      state.passes >= 2,
  };
}

/*
  One full generation:

  500 creatures
       ↓
  shuffle
       ↓
  250 games
       ↓
  each winner produces two mutated children
       ↓
  500 creatures again
*/
function runGeneration(
  population,
  size,
  generation
) {
  const shuffled =
    shuffle([...population]);

  const children = [];

  let blackWins = 0;
  let whiteWins = 0;

  let totalMoves = 0;
  let passFinishes = 0;

  let largestMargin = -Infinity;
  let representative =
    population[0];

  for (
    let i = 0;
    i < shuffled.length;
    i += 2
  ) {
    const a = shuffled[i];
    const b = shuffled[i + 1];

    const result =
      playEvolutionGame(
        a,
        b,
        size
      );

    if (
      result.score.winner === 1
    ) {
      blackWins++;
    } else {
      whiteWins++;
    }

    totalMoves +=
      result.moves;

    if (result.endedByPass) {
      passFinishes++;
    }

    if (
      result.score.margin >
      largestMargin
    ) {
      largestMargin =
        result.score.margin;

      representative =
        result.winner;
    }

    /*
      Winner gets two children.
      Loser gets zero.
    */
    children.push(
      mutatedCopy(
        result.winner,
        generation + 1
      )
    );

    children.push(
      mutatedCopy(
        result.winner,
        generation + 1
      )
    );
  }

  return {
    population: children,

    representative:
      cloneGenome(
        representative
      ),

    stats: {
      blackWins,
      whiteWins,

      averageMoves:
        totalMoves /
        (POPULATION_SIZE / 2),

      passRate:
        passFinishes /
        (POPULATION_SIZE / 2),

      largestMargin,
    },
  };
}

function serializePopulation(
  population,
  representative,
  generation,
  size,
  generationsAtSize
) {
  return JSON.stringify({
    population:
      population.map(
        (genome) =>
          Array.from(
            genome.params
          )
      ),

    representative:
      Array.from(
        representative.params
      ),

    generation,
    size,
    generationsAtSize,
  });
}

function deserializePopulation(text) {
  const data =
    JSON.parse(text);

  if (
    !Array.isArray(
      data.population
    ) ||
    data.population.length !==
      POPULATION_SIZE
  ) {
    throw new Error(
      "Saved population has the wrong size."
    );
  }

  const population =
    data.population.map(
      (params) => ({
        params:
          Float64Array.from(
            params
          ),

        birthGeneration:
          data.generation || 0,
      })
    );

  for (const genome of population) {
    if (
      genome.params.length !==
      PARAM_COUNT
    ) {
      throw new Error(
        "Saved genomes have the wrong number of parameters."
      );
    }
  }

  const representative = {
    params:
      Float64Array.from(
        data.representative
      ),

    birthGeneration:
      data.generation || 0,
  };

  return {
    population,
    representative,

    generation:
      data.generation || 0,

    size:
      data.size || MIN_SIZE,

    generationsAtSize:
      data.generationsAtSize || 0,
  };
}

function App() {
  const canvasRef =
    useRef(null);

  const populationRef =
    useRef(
      createPopulation()
    );

  const representativeRef =
    useRef(
      createBaseGenome()
    );

  const gameRef =
    useRef(
      createGame(MIN_SIZE)
    );

  const trainingRef =
    useRef(false);

  const [mode, setMode] =
    useState("train");

  const [training, setTraining] =
    useState(false);

  const [generation, setGeneration] =
    useState(0);

  const [
    curriculumSize,
    setCurriculumSize,
  ] = useState(MIN_SIZE);

  const [
    generationsAtSize,
    setGenerationsAtSize,
  ] = useState(0);

  const [
    generationsPerSize,
    setGenerationsPerSize,
  ] = useState(20);

  const [lastStats, setLastStats] =
    useState(null);

  const [status, setStatus] =
    useState(
      "Ready to evolve."
    );

  const [boardSize, setBoardSize] =
    useState(MIN_SIZE);

  const [humanColor, setHumanColor] =
    useState(1);

  const [renderTick, setRenderTick] =
    useState(0);

  const draw = useCallback(() => {
    const canvas =
      canvasRef.current;

    if (!canvas) return;

    const ctx =
      canvas.getContext("2d");

    const state =
      gameRef.current;

    const size =
      state.size;

    const padding = 28;

    const step =
      (
        canvas.width -
        padding * 2
      ) /
      (size - 1);

    ctx.clearRect(
      0,
      0,
      canvas.width,
      canvas.height
    );

    ctx.fillStyle =
      "#d9a75f";

    ctx.fillRect(
      0,
      0,
      canvas.width,
      canvas.height
    );

    ctx.strokeStyle =
      "#222";

    ctx.lineWidth = 1;

    for (
      let i = 0;
      i < size;
      i++
    ) {
      const p =
        padding +
        i * step;

      ctx.beginPath();

      ctx.moveTo(
        padding,
        p
      );

      ctx.lineTo(
        canvas.width -
          padding,
        p
      );

      ctx.stroke();

      ctx.beginPath();

      ctx.moveTo(
        p,
        padding
      );

      ctx.lineTo(
        p,
        canvas.height -
          padding
      );

      ctx.stroke();
    }

    const radius =
      Math.max(
        5,
        step * 0.43
      );

    for (
      let i = 0;
      i < state.board.length;
      i++
    ) {
      const value =
        state.board[i];

      if (value === 0) {
        continue;
      }

      const x =
        padding +
        (i % size) *
          step;

      const y =
        padding +
        Math.floor(
          i / size
        ) *
          step;

      ctx.beginPath();

      ctx.arc(
        x,
        y,
        radius,
        0,
        Math.PI * 2
      );

      ctx.fillStyle =
        value === 1
          ? "#111"
          : "#f8f8f8";

      ctx.fill();

      ctx.strokeStyle =
        "#111";

      ctx.stroke();
    }
  }, []);

  useEffect(() => {
    draw();
  }, [
    draw,
    renderTick,
    mode,
    boardSize,
  ]);

  useEffect(() => {
    try {
      const saved =
        localStorage.getItem(
          STORAGE_KEY
        );

      if (!saved) return;

      const loaded =
        deserializePopulation(
          saved
        );

      populationRef.current =
        loaded.population;

      representativeRef.current =
        loaded.representative;

      setGeneration(
        loaded.generation
      );

      setCurriculumSize(
        loaded.size
      );

      setGenerationsAtSize(
        loaded.generationsAtSize
      );

      setStatus(
        `Loaded generation ${loaded.generation}.`
      );
    } catch (error) {
      console.error(error);

      setStatus(
        "Could not load saved evolution."
      );
    }
  }, []);

  function stopTraining() {
    trainingRef.current = false;
    setTraining(false);
  }

  function saveEvolution(
    newGeneration,
    size,
    atSize
  ) {
    try {
      const text =
        serializePopulation(
          populationRef.current,
          representativeRef.current,
          newGeneration,
          size,
          atSize
        );

      localStorage.setItem(
        STORAGE_KEY,
        text
      );
    } catch (error) {
      console.error(
        "Could not save:",
        error
      );
    }
  }

  function startTraining() {
    if (
      trainingRef.current
    ) {
      return;
    }

    trainingRef.current = true;
    setTraining(true);
    setMode("train");

    let currentGeneration =
      generation;

    let currentSize =
      curriculumSize;

    let currentAtSize =
      generationsAtSize;

    setStatus(
      "Evolution running..."
    );

    /*
      One generation runs hundreds of
      games, so we intentionally run
      ONE generation per browser task.

      This keeps the page responsive.
    */
    const runNextGeneration =
      () => {
        if (
          !trainingRef.current
        ) {
          return;
        }

        const start =
          performance.now();

        const result =
          runGeneration(
            populationRef.current,
            currentSize,
            currentGeneration
          );

        populationRef.current =
          result.population;

        representativeRef.current =
          result.representative;

        currentGeneration++;
        currentAtSize++;

        /*
          Curriculum:
          7, 8, 9, ..., 19.

          You can change the number of
          generations spent at each size
          from the UI.
        */
        if (
          currentAtSize >=
            generationsPerSize &&
          currentSize <
            MAX_SIZE
        ) {
          currentSize++;
          currentAtSize = 0;
        }

        const elapsed =
          performance.now() -
          start;

        setGeneration(
          currentGeneration
        );

        setCurriculumSize(
          currentSize
        );

        setGenerationsAtSize(
          currentAtSize
        );

        setLastStats({
          ...result.stats,
          milliseconds:
            elapsed,
        });

        setStatus(
          `Generation ${currentGeneration} finished in ${(elapsed / 1000).toFixed(
            2
          )} s`
        );

        /*
          Save after each generation.
        */
        saveEvolution(
          currentGeneration,
          currentSize,
          currentAtSize
        );

        setTimeout(
          runNextGeneration,
          0
        );
      };

    setTimeout(
      runNextGeneration,
      0
    );
  }

  function resetEvolution() {
    stopTraining();

    populationRef.current =
      createPopulation();

    representativeRef.current =
      createBaseGenome();

    localStorage.removeItem(
      STORAGE_KEY
    );

    setGeneration(0);

    setCurriculumSize(
      MIN_SIZE
    );

    setGenerationsAtSize(0);

    setLastStats(null);

    setStatus(
      "Evolution reset."
    );
  }

  function resetHumanGame(
    size = boardSize,
    color = humanColor
  ) {
    gameRef.current =
      createGame(size);

    setBoardSize(size);

    setRenderTick(
      (x) => x + 1
    );

    if (color === 1) {
      setStatus(
        "Your turn as Black."
      );
    } else {
      setStatus(
        "Evolutionary player is Black."
      );

      setTimeout(() => {
        botMove();
      }, 20);
    }
  }

  function finishHumanGame() {
    const state =
      gameRef.current;

    if (
      state.passes < 2 &&
      state.moveNumber <
        state.size *
          state.size *
          1.5
    ) {
      return false;
    }

    const score =
      scoreGame(state);

    setStatus(
      `Game over: ${
        score.winner === 1
          ? "Black"
          : "White"
      } wins ${score.black.toFixed(
        1
      )}–${score.white.toFixed(
        1
      )}.`
    );

    return true;
  }

  function botMove() {
    if (
      finishHumanGame()
    ) {
      return;
    }

    const state =
      gameRef.current;

    if (
      state.toPlay ===
      humanColor
    ) {
      return;
    }

    const choice =
      chooseCreatureMove(
        state,
        representativeRef.current
      );

    gameRef.current =
      choice.nextState;

    setRenderTick(
      (x) => x + 1
    );

    if (
      !finishHumanGame()
    ) {
      setStatus(
        `Your turn as ${
          humanColor === 1
            ? "Black"
            : "White"
        }.`
      );
    }
  }

  function humanMove(move) {
    const state =
      gameRef.current;

    if (
      state.toPlay !==
        humanColor ||
      state.passes >= 2
    ) {
      return;
    }

    const next =
      tryMove(
        state,
        move
      );

    if (!next) {
      setStatus(
        "Illegal move."
      );

      return;
    }

    gameRef.current =
      next;

    setRenderTick(
      (x) => x + 1
    );

    if (
      !finishHumanGame()
    ) {
      setStatus(
        "Evolutionary player thinking..."
      );

      setTimeout(
        botMove,
        20
      );
    }
  }

  function handleCanvasClick(
    event
  ) {
    if (mode !== "play") {
      return;
    }

    const canvas =
      canvasRef.current;

    const rect =
      canvas.getBoundingClientRect();

    const state =
      gameRef.current;

    const padding = 28;

    const step =
      (
        canvas.width -
        padding * 2
      ) /
      (state.size - 1);

    const x =
      Math.round(
        (
          event.clientX -
          rect.left -
          padding
        ) /
          step
      );

    const y =
      Math.round(
        (
          event.clientY -
          rect.top -
          padding
        ) /
          step
      );

    if (
      x < 0 ||
      y < 0 ||
      x >= state.size ||
      y >= state.size
    ) {
      return;
    }

    humanMove(
      indexOf(
        x,
        y,
        state.size
      )
    );
  }

  function enterPlayMode() {
    stopTraining();

    setMode("play");

    resetHumanGame(
      boardSize,
      humanColor
    );
  }

  return (
    <div
      style={{
        maxWidth: 1050,
        margin: "0 auto",
        padding: 16,
        fontFamily:
          "system-ui, sans-serif",
      }}
    >
      <h1>
        Evolutionary Go
      </h1>

      <p>
        1,000 parametric Go
        creatures evolve by
        tournament selection.
      </p>

      <div
        style={{
          display: "flex",
          flexWrap: "wrap",
          gap: 20,
          alignItems:
            "flex-start",
        }}
      >
        <canvas
          ref={canvasRef}
          width={520}
          height={520}
          onClick={
            handleCanvasClick
          }
          style={{
            border:
              "1px solid #333",
            maxWidth: "100%",
            height: "auto",

            cursor:
              mode === "play"
                ? "crosshair"
                : "default",
          }}
        />

        <div
          style={{
            flex: 1,
            minWidth: 300,
          }}
        >
          <h2>
            {mode === "train"
              ? "Evolution"
              : "Play"}
          </h2>

          <p>
            <strong>
              Status:
            </strong>{" "}
            {status}
          </p>

          {mode ===
          "train" ? (
            <>
              <p>
                <strong>
                  Population:
                </strong>{" "}
                {POPULATION_SIZE}
              </p>

              <p>
                <strong>
                  Generation:
                </strong>{" "}
                {generation}
              </p>

              <p>
                <strong>
                  Board:
                </strong>{" "}
                {curriculumSize}×
                {curriculumSize}
              </p>

              <p>
                <strong>
                  Generations at
                  this size:
                </strong>{" "}
                {generationsAtSize}/
                {generationsPerSize}
              </p>

              <label>
                Generations before
                next board size:{" "}
                <input
                  type="number"
                  min="1"
                  max="10000"
                  value={
                    generationsPerSize
                  }
                  disabled={
                    training
                  }
                  onChange={(
                    event
                  ) =>
                    setGenerationsPerSize(
                      Math.max(
                        1,
                        Number(
                          event
                            .target
                            .value
                        ) || 20
                      )
                    )
                  }
                />
              </label>

              {lastStats && (
                <div
                  style={{
                    marginTop: 15,
                  }}
                >
                  <p>
                    <strong>
                      Last
                      generation:
                    </strong>
                  </p>

                  <p>
                    Black wins:{" "}
                    {
                      lastStats.blackWins
                    }
                    /{POPULATION_SIZE / 2}
                  </p>

                  <p>
                    White wins:{" "}
                    {
                      lastStats.whiteWins
                    }
                    /{POPULATION_SIZE / 2}
                  </p>

                  <p>
                    Games ending
                    by two passes:{" "}
                    {(
                      lastStats.passRate *
                      100
                    ).toFixed(1)}
                    %
                  </p>

                  <p>
                    Average game
                    length:{" "}
                    {lastStats.averageMoves.toFixed(
                      1
                    )}
                  </p>

                  <p>
                    Generation
                    time:{" "}
                    {(
                      lastStats.milliseconds /
                      1000
                    ).toFixed(2)}
                    s
                  </p>
                </div>
              )}

              <button
                onClick={
                  training
                    ? stopTraining
                    : startTraining
                }
              >
                {training
                  ? "Stop evolution"
                  : "Start evolution"}
              </button>{" "}

              <button
                className="play-creature-button"
                onClick={
                  enterPlayMode
                }
              >
                Play current
                creature
              </button>{" "}

              <button
                onClick={
                  resetEvolution
                }
              >
                Reset evolution
              </button>
            </>
          ) : (
            <>
              <label>
                Board size:{" "}
                <select
                  value={
                    boardSize
                  }
                  onChange={(
                    event
                  ) => {
                    const size =
                      Number(
                        event
                          .target
                          .value
                      );

                    setBoardSize(
                      size
                    );

                    setTimeout(
                      () =>
                        resetHumanGame(
                          size,
                          humanColor
                        ),
                      0
                    );
                  }}
                >
                  {Array.from(
                    {
                      length:
                        MAX_SIZE -
                        MIN_SIZE +
                        1,
                    },
                    (_, i) =>
                      MIN_SIZE +
                      i
                  ).map(
                    (size) => (
                      <option
                        key={
                          size
                        }
                        value={
                          size
                        }
                      >
                        {size}×
                        {size}
                      </option>
                    )
                  )}
                </select>
              </label>

              <br />
              <br />

              <label>
                Your color:{" "}
                <select
                  value={
                    humanColor
                  }
                  onChange={(
                    event
                  ) => {
                    const color =
                      Number(
                        event
                          .target
                          .value
                      );

                    setHumanColor(
                      color
                    );

                    setTimeout(
                      () =>
                        resetHumanGame(
                          boardSize,
                          color
                        ),
                      0
                    );
                  }}
                >
                  <option
                    value={1}
                  >
                    Black
                  </option>

                  <option
                    value={-1}
                  >
                    White
                  </option>
                </select>
              </label>

              <br />
              <br />

              <button
                onClick={() =>
                  resetHumanGame(
                    boardSize,
                    humanColor
                  )
                }
              >
                New game
              </button>{" "}

              <button
                onClick={() =>
                  humanMove(
                    PASS
                  )
                }
              >
                Pass
              </button>{" "}

              <button
                onClick={() => {
                  setMode(
                    "train"
                  );

                  setStatus(
                    "Evolution paused."
                  );
                }}
              >
                Back
              </button>

              <p>
                Captures —
                Black:{" "}
                {
                  gameRef.current
                    .captures
                    .black
                }
                , White:{" "}
                {
                  gameRef.current
                    .captures
                    .white
                }
              </p>

              <p>
                Move:{" "}
                {
                  gameRef.current
                    .moveNumber
                }
              </p>
            </>
          )}
        </div>
      </div>

      <details
        style={{
          marginTop: 20,
        }}
      >
        <summary>
          Evolution rules
        </summary>

        <p>
          Each generation,
          the {POPULATION_SIZE}{" "}
          creatures are randomly
          shuffled into{" "}
          {POPULATION_SIZE / 2}{" "}
          pairs. Each pair plays
          one game.
          The loser has no
          descendants. The
          winner produces two
          descendants.
        </p>

        <p>
          Whenever a descendant
          is created, every
          parameter independently
          has a 5% chance of
          mutation. A mutation
          multiplies that
          parameter by a random
          factor between 0.9 and
          1.1.
        </p>

        <p>
          The creature can
          observe captures,
          liberties, atari,
          connections, cuts,
          immediate capture
          danger, territory,
          contested regions,
          eyes, board position,
          game phase, and whether
          passing is sensible.
          Evolution decides the
          weights.
        </p>
      </details>
    </div>
  );
}

export default App;
