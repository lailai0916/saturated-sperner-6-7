'use strict';

const ALL_ROWS = 31;

const FIRST_ROWS = [10, 10, 13, 18, 21];
const SECOND_ROWS = [10, 13, 18, 21, 26];

const FIRST_EXPECTED = [
  [1, 10], [1, 14], [2, 9], [2, 13], [5, 10], [5, 14], [6, 9],
  [6, 13], [9, 10], [9, 14], [9, 18], [10, 13], [10, 17], [13, 14],
  [1, 2, 8], [1, 2, 12], [1, 6, 8], [1, 6, 12], [1, 8, 18],
  [1, 12, 18], [2, 5, 8], [2, 5, 12], [2, 8, 17], [2, 12, 17],
  [5, 6, 8], [5, 6, 12], [5, 8, 18], [5, 12, 18], [6, 8, 17],
  [6, 12, 17], [8, 17, 18], [12, 17, 18],
];

const SECOND_EXPECTED = [[5], [1, 4], [1, 6], [4, 9], [6, 9]];

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function popcount(value) {
  let count = 0;
  for (let x = value; x !== 0; x >>>= 1) count += x & 1;
  return count;
}

function tupleCompare(left, right) {
  if (left.length !== right.length) return left.length - right.length;
  for (let i = 0; i < left.length; i += 1) {
    if (left[i] !== right[i]) return left[i] - right[i];
  }
  return 0;
}

function canonicalTuples(tuples) {
  return tuples
    .map((tuple) => [...tuple].sort((left, right) => left - right))
    .sort(tupleCompare);
}

function tupleKey(tuples) {
  return JSON.stringify(canonicalTuples(tuples));
}

function endpointSupports(rows) {
  return [1, 2, 4, 8, 16].map((endpoint) => {
    let support = 0;
    rows.forEach((row, index) => {
      if ((row & endpoint) !== 0) support |= 1 << index;
    });
    return support;
  });
}

function allowedSupport(endpointRowSupports, support) {
  return support !== 0
    && popcount(support) <= 3
    && endpointRowSupports.every(
      (endpointSupport) => (endpointSupport | support) !== ALL_ROWS,
    );
}

function allowedSupports(rows) {
  const endpoints = endpointSupports(rows);
  return Array.from({ length: ALL_ROWS }, (_, index) => index + 1)
    .filter((support) => allowedSupport(endpoints, support));
}

function pairFree(supports) {
  for (let i = 0; i < supports.length; i += 1) {
    for (let j = i + 1; j < supports.length; j += 1) {
      if ((supports[i] | supports[j]) === ALL_ROWS) return false;
    }
  }
  return true;
}

function completedRows(baseRows, supports) {
  const rows = [...baseRows];
  supports.forEach((support, outsideIndex) => {
    const point = 1 << (5 + outsideIndex);
    for (let row = 0; row < 5; row += 1) {
      if ((support & (1 << row)) !== 0) rows[row] |= point;
    }
  });
  return rows;
}

function rowSizesAtLeastThree(baseRows, supports) {
  return baseRows.every((row, rowIndex) => {
    const outsideCount = supports.reduce(
      (count, support) => count + ((support >> rowIndex) & 1),
      0,
    );
    return popcount(row) + outsideCount >= 3;
  });
}

function isClutter(rows) {
  for (let i = 0; i < rows.length; i += 1) {
    for (let j = 0; j < rows.length; j += 1) {
      if (i !== j && (rows[i] & rows[j]) === rows[i]) return false;
    }
  }
  return true;
}

function completionCore(baseRows, supports) {
  return rowSizesAtLeastThree(baseRows, supports)
    && isClutter(completedRows(baseRows, supports));
}

function validCompletion(baseRows, supports) {
  if (!pairFree(supports) || !completionCore(baseRows, supports)) return false;

  return supports.every((_, removedIndex) => {
    const reduced = supports.filter((__, index) => index !== removedIndex);
    return !completionCore(baseRows, reduced);
  });
}

function enumerateMinimalCompletions(baseRows) {
  const supports = allowedSupports(baseRows);
  const completions = [];
  const subsetCount = 2 ** supports.length;

  for (let subset = 1; subset < subsetCount; subset += 1) {
    const chosen = supports.filter((_, index) => (subset & (1 << index)) !== 0);
    if (validCompletion(baseRows, chosen)) completions.push(chosen);
  }

  return {
    allowedSupports: supports,
    subsetsScanned: subsetCount,
    completions: canonicalTuples(completions),
  };
}

function firstStructuralNormalForm() {
  const left = [1, 5, 9, 13, 17];
  const right = [2, 6, 10, 14, 18];
  const separate = [8, 12];
  const completions = [];

  for (const leftSupport of left) {
    for (const rightSupport of right) {
      if ((leftSupport & 8) !== 0 || (rightSupport & 8) !== 0) {
        const candidate = [leftSupport, rightSupport];
        if (pairFree(candidate)) completions.push(candidate);
      } else {
        for (const separateSupport of separate) {
          const candidate = [leftSupport, rightSupport, separateSupport];
          if (pairFree(candidate)) completions.push(candidate);
        }
      }
    }
  }

  return canonicalTuples(completions);
}

function secondStructuralNormalForm() {
  const completions = [[5]];
  for (const rowZeroWitness of [1, 9]) {
    for (const rowTwoWitness of [4, 6]) {
      const candidate = [rowZeroWitness, rowTwoWitness];
      if (pairFree(candidate)) completions.push(candidate);
    }
  }
  return canonicalTuples(completions);
}

function sizeHistogram(tuples) {
  const histogram = {};
  for (const tuple of tuples) {
    histogram[tuple.length] = (histogram[tuple.length] ?? 0) + 1;
  }
  return histogram;
}

function audit(name, baseRows, expected, structural) {
  const brute = enumerateMinimalCompletions(baseRows);
  const expectedCanonical = canonicalTuples(expected);

  assert(
    tupleKey(brute.completions) === tupleKey(expectedCanonical),
    `${name}: brute-force list differs from expected list`,
  );
  assert(
    tupleKey(structural) === tupleKey(expectedCanonical),
    `${name}: structural normal form differs from expected list`,
  );
  assert(
    structural.every((supports) => validCompletion(baseRows, supports)),
    `${name}: structural list contains a non-minimal or pair-illegal completion`,
  );

  return {
    endpoint_row_supports: endpointSupports(baseRows),
    allowed_support_count: brute.allowedSupports.length,
    allowed_supports: brute.allowedSupports,
    subsets_scanned: brute.subsetsScanned,
    minimal_completion_count: brute.completions.length,
    completion_size_histogram: sizeHistogram(brute.completions),
    structural_exact_match: true,
    expected_exact_match: true,
    completions: brute.completions,
  };
}

const first = audit(
  'first parallel class',
  FIRST_ROWS,
  FIRST_EXPECTED,
  firstStructuralNormalForm(),
);
const second = audit(
  'second parallel class',
  SECOND_ROWS,
  SECOND_EXPECTED,
  secondStructuralNormalForm(),
);

assert(first.allowed_support_count === 16, 'first: unexpected allowed-support count');
assert(first.subsets_scanned === 65536, 'first: incomplete exhaustive scan');
assert(first.minimal_completion_count === 32, 'first: expected 32 completions');
assert(
  first.completion_size_histogram[2] === 14
    && first.completion_size_histogram[3] === 18,
  'first: expected 14 two-point and 18 three-point completions',
);
assert(
  first.completions.every((completion) => (
    completion.filter((support) => (support & 3) === 3).length === 0
  )),
  'first: hidden both-side witness survived minimality',
);

assert(second.allowed_support_count === 14, 'second: unexpected allowed-support count');
assert(second.subsets_scanned === 16384, 'second: incomplete exhaustive scan');
assert(second.minimal_completion_count === 5, 'second: expected 5 completions');
assert(
  second.completion_size_histogram[1] === 1
    && second.completion_size_histogram[2] === 4,
  'second: expected one combined and four separate completions',
);

console.log(JSON.stringify({
  schema: 'p0054.g4.13.p3k2-normal-form-audit.v1',
  epistemic_label: 'PROVED_CANDIDATE_NORMAL_FORM_PLUS_COMPUTED_EXACT_CROSSCHECK',
  first_parallel_class: first,
  second_parallel_class: second,
  hidden_both_side_witnesses: 0,
  mismatches: 0,
}, null, 2));
