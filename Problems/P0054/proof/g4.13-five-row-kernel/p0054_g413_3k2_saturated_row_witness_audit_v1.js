'use strict';

const CLASSES = [
  {rows: [21, 21, 26, 38, 41], missed: 26, witness: 5},
  {rows: [21, 23, 26, 38, 41], missed: 21, witness: 10},
  {rows: [21, 26, 31, 38, 41], missed: 21, witness: 10},
  {rows: [21, 26, 38, 41, 63], missed: 21, witness: 10},
];

function popcount(value) {
  let count = 0;
  while (value) {
    count += value & 1;
    value >>= 1;
  }
  return count;
}

function blockers(rows) {
  const result = [];
  for (let candidate = 1; candidate < 64; candidate += 1) {
    if (!rows.every((row) => row & candidate)) continue;
    const minimal = [...Array(6).keys()]
      .filter((point) => candidate & (1 << point))
      .every((point) => !rows.every((row) => row & (candidate ^ (1 << point))));
    if (minimal) result.push(candidate);
  }
  return result;
}

function endpointDegrees(blockerList) {
  return [...Array(6).keys()].map(
    (point) => blockerList.filter((blocker) => blocker & (1 << point)).length,
  );
}

function support(rows, point) {
  return rows.reduce(
    (mask, row, rowIndex) => mask | ((row & (1 << point)) ? 1 << rowIndex : 0),
    0,
  );
}

function pairType(rows, left, right) {
  const leftSupport = support(rows, left);
  const rightSupport = support(rows, right);
  if ((leftSupport | rightSupport) !== 31) throw new Error('pair does not cover rows');
  if ((leftSupport & rightSupport) === 0) return 'D';
  if (popcount(leftSupport) === 3
      && popcount(rightSupport) === 3
      && popcount(leftSupport & rightSupport) === 1) return 'I';
  throw new Error('unexpected pair type');
}

const result = CLASSES.map((entry, index) => {
  const dual = blockers(entry.rows);
  const degrees = endpointDegrees(dual);
  const missedIndices = entry.rows
    .map((row, rowIndex) => ({row, rowIndex}))
    .filter(({row}) => row === entry.missed)
    .map(({rowIndex}) => rowIndex);
  const witnessIntersections = entry.rows.map((row) => row & entry.witness);
  const iPairs = [[0, 1], [2, 3], [4, 5]]
    .filter(([left, right]) => pairType(entry.rows, left, right) === 'I')
    .length;
  return {
    class: index + 1,
    rows: entry.rows,
    type_i_pairs: iPairs,
    endpoint_blockers: dual,
    endpoint_blocker_count: dual.length,
    endpoint_degrees: degrees,
    missed_row_mask: entry.missed,
    missed_row_indices: missedIndices,
    witness_mask: entry.witness,
    witness_intersections: witnessIntersections,
    witness_misses_selected_row: missedIndices.some(
      (rowIndex) => witnessIntersections[rowIndex] === 0,
    ),
    witness_meets_every_other_row: missedIndices.some(
      (rowIndex) => witnessIntersections.every(
        (intersection, otherIndex) => otherIndex === rowIndex || intersection !== 0,
      ),
    ),
  };
});

for (const [index, entry] of result.entries()) {
  if (entry.type_i_pairs !== index) throw new Error('type-I count mismatch');
  if (entry.endpoint_blocker_count !== 7) throw new Error('blocker count mismatch');
  if (entry.endpoint_degrees.some((degree) => degree !== 3)) {
    throw new Error('endpoint degree mismatch');
  }
  if (!entry.witness_misses_selected_row || !entry.witness_meets_every_other_row) {
    throw new Error('row-witness mismatch');
  }
}

process.stdout.write(`${JSON.stringify({
  schema: 'p0054.g4.13.3k2-saturated-row-witness-audit.v1',
  epistemic_label: 'COMPUTED_EXACT_CROSSCHECK',
  classes: result,
}, null, 2)}\n`);
