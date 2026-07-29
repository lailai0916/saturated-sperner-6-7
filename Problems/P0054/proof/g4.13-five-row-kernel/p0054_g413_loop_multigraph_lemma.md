# P0054 G4.13 scratch: five-vertex loop-multigraph lemma

```text
STATUS: PROVED_CANDIDATE
SCOPE: DEGREE_AT_MOST_TWO_BRANCH_OF_THE_FIVE_ROW_KERNEL
RESULT: AT_LEAST_NINE_MINIMAL_ACTUAL_EDGE_COVERS
NETWORK: MATHEMATICS_OFFLINE
```

## Statement

Let $J$ be a finite loop-multigraph on five vertices. Loops and nonloop
edges are actual objects, so parallel copies remain distinct. Count a loop
once in the degree of its vertex. Assume:

- every vertex has degree at least three;
- $J$ is inclusion-minimal with this property.

Then $J$ has at least nine minimal actual edge covers.

Every positive edge touches a degree-three vertex. Otherwise deleting that
edge would leave every degree at least three. Let $L$ be the degree-three
vertices and put $l=|L|$. Every vertex outside $L$ has degree at least four,
and every one of its incidences consumes an incidence in $L$. Hence

$$
4(5-l)\le3l
\tag{1}
$$

Thus $l\in\set{3,4,5}$.

## Four-selector lemma

Fix four degree-three vertices $L=\set{1,2,3,4}$ and a fifth vertex $h$.
Assume $h$ has no loop and every edge at $h$ joins it to $L$. For every
$i\in L$, choose one of the three actual edges incident with $i$.

Consider only choices whose image covers $h$. Every such image is an edge
cover and therefore contains a minimal edge cover $C$. A fixed $C$ lies in
the image of at most seven choices.

Indeed, the image has at most four edges, while three edges are necessary to
cover five vertices.

- If $|C|=4$, the four selectors must select the four edges bijectively.
  Minimality gives every edge a private vertex. If $h$ is private for one
  edge, its low endpoint is forced and the other three edges have three
  distinct private low vertices. If $h$ is not private, all four edges have
  distinct private low vertices. In either case the choice is unique.
- If $|C|=3$ and $C$ contains a loop, it consists of that loop and two
  disjoint nonloop edges. The loop vertex and the low endpoint of the edge
  through $h$ are forced. Either endpoint may select the remaining edge, and
  the other endpoint has three choices. Inclusion-exclusion gives
  $3+3-1=5$ choices.
- If $|C|=3$ and $C$ has no loop, it is a two-edge path plus a disjoint edge.
  If $h$ lies in the path, two low selectors are forced and the disjoint edge
  again gives five choices. If $h$ lies in the disjoint edge, its low endpoint
  is forced. On the low three-vertex path, the center may select the first
  edge, the second edge, or its third available edge. These cases contribute
  $3$, $3$, and $1$ choices, for a total of seven.

Counting pairs consisting of a valid choice and a contained minimal edge
cover therefore gives

$$
|B(J)|\ge\left\lceil\frac{Q}{7}\right\rceil
\tag{2}
$$

where $Q$ is the number of valid choices.

## Three low vertices

Let the two high vertices be $u,v$. No edge joins two low vertices, because
the nine low incidences must supply at least eight high incidences. The only
remaining incidence may be a low loop.

For low vertex $i$, let $a_i,b_i,c_i$ count its actual edges to $u$, its
actual edges to $v$, and its loops. Then

$$
\begin{aligned}
  a_i+b_i+c_i & =3 \\
  \sum_i a_i & \ge4 \\
  \sum_i b_i & \ge4
\end{aligned}
\tag{3}
$$

Choose one actual edge at each low vertex. The number of choices covering
both high vertices is

$$
27-\prod_i(3-a_i)-\prod_i(3-b_i)+\prod_i c_i
\tag{4}
$$

For three integers $0\le a_i\le3$ with sum at least four,
$\prod_i(3-a_i)\le4$. The maximum occurs at a permutation of $(1,1,2)$.
The same bound holds for the $b_i$. Thus (4) is at least nineteen.

Every such choice is already a minimal edge cover: its three actual edges
are distinct, cover both high vertices, and have distinct private low
vertices. Hence $J$ has at least nineteen minimal edge covers.

## Four low vertices

Let $h$ be the high vertex and let $a_i$ count the actual edges from low
vertex $i$ to $h$. Then

$$
\sum_{i=1}^4a_i\ge4
\tag{5}
$$

Among the $3^4=81$ four-selector choices, exactly

$$
Q=81-\prod_{i=1}^4(3-a_i)
\tag{6}
$$

cover $h$. Subject to (5), the product in (6) is at most sixteen. The
four-selector lemma gives

$$
|B(J)|\ge\left\lceil\frac{65}{7}\right\rceil=10
\tag{7}
$$

## Five low vertices

Every vertex now has degree three. Suppose first that some vertex $h$ has no
loop. Its three actual incident edges join it to the other four vertices.
If their multiplicities are $a_1,\dots,a_4$, then

$$
\begin{aligned}
  \sum_{i=1}^4a_i & =3 \\
  \prod_{i=1}^4(3-a_i) & \le24
\end{aligned}
\tag{8}
$$

Use the other four vertices as selectors. At least $81-24=57$ choices cover
$h$. The four-selector lemma gives

$$
|B(J)|\ge\left\lceil\frac{57}{7}\right\rceil=9
\tag{9}
$$

It remains that every vertex has a loop. Let $q_i\in\set{1,2,3}$ be its loop
multiplicity. There are $\prod_iq_i$ all-loop minimal covers. Also,
$\sum_iq_i$ is odd because the remaining incidence sum is even. If
$\prod_iq_i\ge9$, the result follows. Up to permutation, the only remaining
vectors are

$$
\begin{aligned}
  &(1,1,1,1,1) \\
  &(3,1,1,1,1) \\
  &(2,2,1,1,1)
\end{aligned}
\tag{10}
$$

Delete the loops and call the resulting loopless multigraph $G$.

- For $(1,1,1,1,1)$, every vertex has $G$-degree two. Hence $G$ is either a
  five-cycle or a triangle plus a two-cycle of parallel actual edges. In the
  five-cycle, the all-loop cover, the five covers formed by one loop and the
  unique perfect matching after deleting its vertex, and the five covers
  formed by a complementary edge and two-edge path give eleven covers. In
  the second graph, the all-loop cover and the six covers formed by a
  triangle loop and a perfect matching already give seven. Choosing one of
  the two parallel edges and two edges of the triangle gives six more.
- For $(3,1,1,1,1)$, the vertex with three loops is isolated in $G$. The
  other four vertices induce either a four-cycle or two disjoint two-cycles,
  and therefore have at least two perfect matchings. The three all-loop
  covers and the six covers formed by one of the three loops at the isolated
  vertex and one of those perfect matchings give at least nine.
- For $(2,2,1,1,1)$, the degrees in $G$ are $(1,1,2,2,2)$. Thus $G$ is a
  five-vertex path, a three-vertex path plus a two-cycle, or an edge plus a
  triangle. There are four all-loop covers. In the first case, deleting an
  endpoint, the middle vertex, or the other endpoint leaves a unique perfect
  matching; their loop multiplicities give $2+1+2=5$ further covers. In the
  second case, either endpoint loop followed by a perfect matching gives
  eight further covers. In the last case, deleting any triangle vertex gives
  three further covers, and the isolated edge together with any two edges of
  the triangle gives another three.

All cases contain at least nine minimal actual edge covers.

## Evidence boundary

This argument is arbitrary-finite and preserves loops and parallel actual
edges. It replaces the `COMPUTED` five-vertex support-multiplicity minima
$19,16,15$ only where the G4.13 five-row pair lemma needs the weaker lower
bound nine. It does not alter the G4.12 frozen artifacts or any global claim.
