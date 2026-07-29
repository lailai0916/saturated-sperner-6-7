'use strict';

const FIRST_BASE = {
  a: 20,
  p: 11,
  q: 20,
  u: 7,
  v: 24,
};

const SECOND_BASE = {
  a: 10,
  p: 21,
  q: 10,
  u: 19,
  v: 28,
};

const FIRST_PATTERNS = [
  [1, 10], [1, 14], [2, 9], [2, 13], [5, 10], [5, 14], [6, 9],
  [6, 13], [9, 10], [9, 14], [9, 18], [10, 13], [10, 17], [13, 14],
  [1, 2, 8], [1, 2, 12], [1, 6, 8], [1, 6, 12], [1, 8, 18],
  [1, 12, 18], [2, 5, 8], [2, 5, 12], [2, 8, 17], [2, 12, 17],
  [5, 6, 8], [5, 6, 12], [5, 8, 18], [5, 12, 18], [6, 8, 17],
  [6, 12, 17], [8, 17, 18], [12, 17, 18],
];

const SECOND_PATTERNS = [[1, 4], [1, 6], [4, 9], [5], [6, 9]];
const ENDPOINTS = ['a', 'p', 'q', 'u', 'v'];

function blockers(supports) {
  const points = Object.keys(supports);
  const result = [];
  for (let subset = 1; subset < (1 << points.length); subset += 1) {
    const selected = points.filter((_, index) => subset & (1 << index));
    const union = selected.reduce((value, point) => value | supports[point], 0);
    if (union !== 31) continue;
    const minimal = selected.every((removed) => {
      const reduced = selected
        .filter((point) => point !== removed)
        .reduce((value, point) => value | supports[point], 0);
      return reduced !== 31;
    });
    if (minimal) result.push(selected);
  }
  return result;
}

function endpointDegrees(base, pattern) {
  const supports = {...base};
  pattern.forEach((support, index) => {
    supports[String.fromCharCode('x'.charCodeAt(0) + index)] = support;
  });
  const degrees = Object.fromEntries(ENDPOINTS.map((point) => [point, 0]));
  for (const blocker of blockers(supports)) {
    for (const point of blocker) {
      if (point in degrees) degrees[point] += 1;
    }
  }
  return degrees;
}

function computedLegal(base, pattern) {
  return Object.values(endpointDegrees(base, pattern)).every((degree) => degree <= 3);
}

function firstStructuralLegal(pattern) {
  const x0 = pattern.find((support) => support & 1);
  const x1 = pattern.find((support) => support & 2);
  if (pattern.length === 3) {
    const t = pattern.find((support) => !(support & 3));
    return !(t & 4)
      && !(x0 & 16)
      && !(x1 & 16)
      && Boolean(x0 & 4) !== Boolean(x1 & 4);
  }
  return Boolean(x0 & 8) !== Boolean(x1 & 8)
    && !(x0 & 16)
    && !(x1 & 16)
    && !((x0 & 4) && (x1 & 4));
}

function secondStructuralLegal(pattern) {
  if (pattern.length === 1) return pattern[0] === 5;
  const x0 = pattern.find((support) => support & 1);
  const x2 = pattern.find((support) => support & 4);
  return !(x0 & 8) && !(x2 & 2);
}

function audit(patterns, base, structuralLegal) {
  const cases = patterns.map((pattern) => {
    const structural = structuralLegal(pattern);
    const computed = computedLegal(base, pattern);
    return {
      pattern,
      structural_legal: structural,
      computed_legal: computed,
      endpoint_degrees: endpointDegrees(base, pattern),
    };
  });
  return {
    accepted: cases.filter((entry) => entry.computed_legal).map((entry) => entry.pattern),
    rejected: cases.filter((entry) => !entry.computed_legal).map((entry) => entry.pattern),
    mismatches: cases.filter(
      (entry) => entry.structural_legal !== entry.computed_legal,
    ),
    cases,
  };
}

const first = audit(FIRST_PATTERNS, FIRST_BASE, firstStructuralLegal);
const second = audit(SECOND_PATTERNS, SECOND_BASE, secondStructuralLegal);

const result = {
  schema: 'p0054.g4.13.p3k2-endpoint-structural-classifier.v1',
  epistemic_label: 'COMPUTED_EXACT_MATCH_FOR_PROVED_CANDIDATE_CLASSIFIER',
  first: {
    normal_form_count: FIRST_PATTERNS.length,
    accepted_count: first.accepted.length,
    rejected_count: first.rejected.length,
    accepted: first.accepted,
    mismatches: first.mismatches,
  },
  second: {
    normal_form_count: SECOND_PATTERNS.length,
    accepted_count: second.accepted.length,
    rejected_count: second.rejected.length,
    accepted: second.accepted,
    mismatches: second.mismatches,
  },
};

if (first.accepted.length !== 8 || first.rejected.length !== 24) {
  throw new Error('first-class count mismatch');
}
if (second.accepted.length !== 2 || second.rejected.length !== 3) {
  throw new Error('second-class count mismatch');
}
if (first.mismatches.length || second.mismatches.length) {
  throw new Error('structural/computed classifier mismatch');
}

process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
