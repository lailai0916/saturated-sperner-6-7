'use strict';

const ROLE_NAMES = ['a', 'b', 'c', 'd', 'e', 'f'];
const FULL_SUPPORT = 7;
const ANONYMOUS_SUPPORTS = [1, 2, 3, 4, 5, 6, 7];

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function popcount(value) {
  let count = 0;
  for (let x = value; x !== 0; x >>>= 1) count += x & 1;
  return count;
}

function validRolePartition(labels) {
  const distinctPairs = [
    [0, 1], [2, 3], [4, 5],
    [0, 4], [0, 5], [1, 2], [1, 3],
  ];
  return distinctPairs.every(([left, right]) => labels[left] !== labels[right]);
}

function rolePartitions() {
  const result = [];
  const labels = Array(ROLE_NAMES.length).fill(0);

  function visit(index, maximum) {
    if (index === labels.length) {
      if (validRolePartition(labels)) result.push([...labels]);
      return;
    }

    for (let label = 0; label <= maximum + 1; label += 1) {
      labels[index] = label;
      visit(index + 1, Math.max(maximum, label));
    }
  }

  labels[0] = 0;
  visit(1, 0);
  return result;
}

function pointsFromPartition(labels) {
  const pointCount = Math.max(...labels) + 1;
  return Array.from({ length: pointCount }, (_, pointIndex) => {
    const roles = ROLE_NAMES.filter((_, roleIndex) => labels[roleIndex] === pointIndex);
    return {
      name: roles.join('='),
      roles,
      isA: roles.includes('a'),
      isB: roles.includes('b'),
      inC: roles.includes('c') || roles.includes('d'),
      inE: roles.includes('e') || roles.includes('f'),
      budget: 3
        - Number(roles.includes('a'))
        - Number(roles.includes('b'))
        - Number(roles.includes('c') || roles.includes('d'))
        - Number(roles.includes('e') || roles.includes('f')),
    };
  });
}

function supportOptions(budget) {
  return Array.from({ length: 8 }, (_, support) => support)
    .filter((support) => popcount(support) <= budget);
}

function rolePointIndex(labels, role) {
  return labels[ROLE_NAMES.indexOf(role)];
}

function partitionCategory(labels) {
  const label = (role) => rolePointIndex(labels, role);
  const aInC = label('a') === label('c') || label('a') === label('d');
  const bInE = label('b') === label('e') || label('b') === label('f');
  if (aInC || bInE) return 'opposite_endpoint';

  const cPoints = new Set([label('c'), label('d')]);
  const overlap = [label('e'), label('f')].filter((point) => cPoints.has(point)).length;
  if (overlap === 0) return 'no_endpoint_identification';
  if (overlap === 1) return 'one_pair_overlap';
  return 'equal_pairs';
}

function traceConditions(labels, supports) {
  const a = rolePointIndex(labels, 'a');
  const b = rolePointIndex(labels, 'b');
  const c = rolePointIndex(labels, 'c');
  const d = rolePointIndex(labels, 'd');
  const e = rolePointIndex(labels, 'e');
  const f = rolePointIndex(labels, 'f');

  return [1, 2, 4].every((row) => {
    const firstTrace = (supports[b] & row) !== 0
      || ((supports[c] & row) !== 0 && (supports[d] & row) !== 0);
    const secondTrace = (supports[a] & row) !== 0
      || ((supports[e] & row) !== 0 && (supports[f] & row) !== 0);
    return firstTrace && secondTrace;
  });
}

function traceTypesForRows(labels, supports) {
  const index = (role) => rolePointIndex(labels, role);
  return [1, 2, 4].map((row) => {
    const types = [];
    if ((supports[index('a')] & row) !== 0 && (supports[index('b')] & row) !== 0) {
      types.push('A');
    }
    if ((supports[index('a')] & row) !== 0
      && (supports[index('c')] & row) !== 0
      && (supports[index('d')] & row) !== 0) {
      types.push('C');
    }
    if ((supports[index('b')] & row) !== 0
      && (supports[index('e')] & row) !== 0
      && (supports[index('f')] & row) !== 0) {
      types.push('E');
    }
    if ((supports[index('c')] & row) !== 0
      && (supports[index('d')] & row) !== 0
      && (supports[index('e')] & row) !== 0
      && (supports[index('f')] & row) !== 0) {
      types.push('N');
    }
    return types;
  });
}

function rowsFromPoints(points) {
  return [1, 2, 4].map((row) => points
    .map((point, index) => ({ point, index }))
    .filter(({ point }) => (point.support & row) !== 0)
    .map(({ index }) => index));
}

function isClutter(points) {
  const rows = rowsFromPoints(points).map((row) => new Set(row));
  for (let i = 0; i < rows.length; i += 1) {
    for (let j = 0; j < rows.length; j += 1) {
      if (i === j) continue;
      const contained = [...rows[i]].every((point) => rows[j].has(point));
      if (contained) return false;
    }
  }
  return true;
}

function rowSizesAtLeastThree(points) {
  return rowsFromPoints(points).every((row) => row.length >= 3);
}

function goodBlocker(blocker, points) {
  const selected = blocker.map((index) => points[index]);
  const containsA = selected.some((point) => point.isA);
  const containsB = selected.some((point) => point.isB);
  const meetsC = selected.some((point) => point.inC);
  const meetsE = selected.some((point) => point.inE);
  return (!containsA || !meetsE) && (!containsB || !meetsC);
}

function goodBlockerCount(points, stopAt = Number.POSITIVE_INFINITY) {
  let count = 0;

  for (let index = 0; index < points.length; index += 1) {
    if (points[index].support === FULL_SUPPORT && goodBlocker([index], points)) {
      count += 1;
      if (count >= stopAt) return count;
    }
  }

  for (let left = 0; left < points.length; left += 1) {
    if (points[left].support === FULL_SUPPORT) continue;
    for (let right = left + 1; right < points.length; right += 1) {
      if (points[right].support === FULL_SUPPORT) continue;
      if ((points[left].support | points[right].support) !== FULL_SUPPORT) continue;
      if (goodBlocker([left, right], points)) {
        count += 1;
        if (count >= stopAt) return count;
      }
    }
  }

  const bySupport = new Map([1, 2, 4].map((support) => [support, []]));
  points.forEach((point, index) => {
    if (bySupport.has(point.support)) bySupport.get(point.support).push(index);
  });
  for (const first of bySupport.get(1)) {
    for (const second of bySupport.get(2)) {
      for (const third of bySupport.get(4)) {
        if (goodBlocker([first, second, third], points)) {
          count += 1;
          if (count >= stopAt) return count;
        }
      }
    }
  }

  return count;
}

function anonymousPoints(multiplicities) {
  const points = [];
  multiplicities.forEach((multiplicity, supportIndex) => {
    for (let copy = 0; copy < multiplicity; copy += 1) {
      points.push({
        name: `x${supportIndex + 1}_${copy + 1}`,
        support: ANONYMOUS_SUPPORTS[supportIndex],
        isA: false,
        isB: false,
        inC: false,
        inE: false,
      });
    }
  });
  return points;
}

function canDeleteAnonymous(fixedPoints, multiplicities, supportIndex) {
  if (multiplicities[supportIndex] === 0) return false;
  const reduced = [...multiplicities];
  reduced[supportIndex] -= 1;
  const points = [...fixedPoints, ...anonymousPoints(reduced)];
  return rowSizesAtLeastThree(points) && isClutter(points);
}

function minimalAnonymousCompletion(fixedPoints, multiplicities) {
  const points = [...fixedPoints, ...anonymousPoints(multiplicities)];
  if (!rowSizesAtLeastThree(points) || !isClutter(points)) return false;
  return multiplicities.every(
    (_, supportIndex) => !canDeleteAnonymous(fixedPoints, multiplicities, supportIndex),
  );
}

function add(statsList, key, value = 1) {
  statsList.forEach((stats) => {
    stats[key] += value;
  });
}

function minimize(statsList, key, value) {
  statsList.forEach((stats) => {
    stats[key] = Math.min(stats[key], value);
  });
}

function findAnonymousCounterexample(fixedPoints, statsList) {
  const multiplicities = Array(ANONYMOUS_SUPPORTS.length).fill(0);

  function visit(index) {
    if (index === multiplicities.length) {
      add(statsList, 'anonymous_vectors_scanned');
      if (!minimalAnonymousCompletion(fixedPoints, multiplicities)) return null;
      add(statsList, 'minimal_anonymous_completions');
      const points = [...fixedPoints, ...anonymousPoints(multiplicities)];
      const count = goodBlockerCount(points, 2);
      minimize(statsList, 'minimum_good_blockers', count);
      if (count < 2) return { multiplicities: [...multiplicities], points, count };
      return null;
    }

    for (let multiplicity = 0; multiplicity <= 3; multiplicity += 1) {
      multiplicities[index] = multiplicity;
      const result = visit(index + 1);
      if (result !== null) return result;
    }
    return null;
  }

  return visit(0);
}

function auditPartition(labels, globalStats, categoryStats, hardStates) {
  const pointTemplates = pointsFromPartition(labels);
  const supports = Array(pointTemplates.length).fill(0);
  let counterexample = null;
  const statsList = [globalStats, categoryStats];

  add(statsList, 'role_partitions');

  function visit(index) {
    if (counterexample !== null) return;
    if (index === pointTemplates.length) {
      add(statsList, 'fixed_support_assignments');
      if (!traceConditions(labels, supports)) return;
      add(statsList, 'trace_legal_fixed_assignments');

      const fixedPoints = pointTemplates.map((point, pointIndex) => ({
        ...point,
        support: supports[pointIndex],
      }));
      if (goodBlockerCount(fixedPoints, 2) >= 2) {
        add(statsList, 'fixed_assignments_already_closed');
        return;
      }

      add(statsList, 'fixed_assignments_needing_completion');
      hardStates.push({
        category: partitionCategory(labels),
        points: fixedPoints.map((point) => ({ name: point.name, support: point.support })),
        row_trace_types: traceTypesForRows(labels, supports),
      });
      const completion = findAnonymousCounterexample(fixedPoints, statsList);
      if (completion !== null) {
        counterexample = { labels, fixedPoints, ...completion };
      }
      return;
    }

    for (const support of supportOptions(pointTemplates[index].budget)) {
      supports[index] = support;
      visit(index + 1);
      if (counterexample !== null) return;
    }
  }

  visit(0);
  return counterexample;
}

function emptyStats() {
  return {
    role_partitions: 0,
    fixed_support_assignments: 0,
    trace_legal_fixed_assignments: 0,
    fixed_assignments_already_closed: 0,
    fixed_assignments_needing_completion: 0,
    anonymous_vectors_scanned: 0,
    minimal_anonymous_completions: 0,
    minimum_good_blockers: Number.POSITIVE_INFINITY,
  };
}

const partitions = rolePartitions();
const stats = emptyStats();
const breakdown = Object.fromEntries([
  'no_endpoint_identification',
  'opposite_endpoint',
  'one_pair_overlap',
  'equal_pairs',
].map((category) => [category, emptyStats()]));
const hardStates = [];

let counterexample = null;
for (const partition of partitions) {
  const category = partitionCategory(partition);
  counterexample = auditPartition(partition, stats, breakdown[category], hardStates);
  if (counterexample !== null) break;
}

assert(counterexample === null, `trace lemma counterexample: ${JSON.stringify(counterexample)}`);
assert(stats.minimum_good_blockers >= 2, 'a completed clutter has fewer than two good blockers');

console.log(JSON.stringify({
  schema: 'p0054.g4.13.p4-trace-lemma-audit.v1',
  epistemic_label: 'PROVED_CANDIDATE_PLUS_COMPUTED_BOUNDED_EXACT_CROSSCHECK',
  ...stats,
  minimum_good_blockers: stats.minimum_good_blockers,
  breakdown: Object.fromEntries(Object.entries(breakdown).map(([category, values]) => [
    category,
    {
      ...values,
      minimum_good_blockers: Number.isFinite(values.minimum_good_blockers)
        ? values.minimum_good_blockers
        : null,
    },
  ])),
  hard_fixed_states: hardStates,
  counterexamples: 0,
}, null, 2));
