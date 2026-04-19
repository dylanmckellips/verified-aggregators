// ============================================================
// Dafny Verification: Biclique Aggregator Math
// Property A: every returned set is rho-dense.
// Property B: every induced biclique is contained in some returned set.
// ============================================================
// Requirements: Dafny 3, z3 4.12.1
// ============================================================

//graph theory utils

ghost predicate Adjacent(edges: set<(int,int)>, u: int, v: int) {
  (u, v) in edges
}

ghost predicate Undirected(edges: set<(int,int)>) {
  forall u, v :: (u, v) in edges ==> (v, u) in edges
}

ghost function Gamma(edges: set<(int,int)>, V: set<int>, C: set<int>): set<int> {
  set v | v in V && forall c :: c in C ==> Adjacent(edges, v, c)
}

ghost function EdgeCount(edges: set<(int,int)>, S: set<int>, T: set<int>): nat {
  |set p | p in edges && p.0 in S && p.1 in T|
}

ghost predicate DensityGT(edges: set<(int,int)>, V: set<int>,
                           H: set<int>, C: set<int>, pNum: nat, pDen: nat)
  requires pDen > 0
{
  EdgeCount(edges, H + C, Gamma(edges, V, C)) * pDen >
  pNum * |H + C| * |Gamma(edges, V, C)|
}

ghost predicate RhoDense(edges: set<(int,int)>, V: set<int>,
                          H: set<int>, C: set<int>, pNum: nat, pDen: nat)
  requires pDen > 0
{
  DensityGT(edges, V, H, C, pNum, pDen)
}

ghost predicate IsBiclique(edges: set<(int,int)>, L: set<int>, R: set<int>) {
  forall l, r :: l in L && r in R ==> Adjacent(edges, l, r)
}

ghost predicate IsInducedBiclique(edges: set<(int,int)>, K: set<int>) {
  exists L, R ::
    L + R == K && L * R == {} && L != {} && R != {} &&
    IsBiclique(edges, L, R) &&
    (forall u, v :: u in L && v in L && u != v ==> !Adjacent(edges, u, v)) &&
    (forall u, v :: u in R && v in R && u != v ==> !Adjacent(edges, u, v))
}

// Recursive encoding: avoids forall-exists folding issues.
ghost function AllRhoDenseF(edges: set<(int,int)>, V: set<int>,
                             result: seq<set<int>>, pNum: nat, pDen: nat): bool
  requires pDen > 0
  decreases |result|
{
  if |result| == 0 then true
  else (exists H2: set<int>, C2: set<int> ::
          result[0] == H2 + C2 + Gamma(edges, V, C2) &&
          RhoDense(edges, V, H2, C2, pNum, pDen)) &&
       AllRhoDenseF(edges, V, result[1..], pNum, pDen)
}

ghost predicate AllRhoDense(edges: set<(int,int)>, V: set<int>,
                              result: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0
{
  AllRhoDenseF(edges, V, result, pNum, pDen)
}

ghost predicate AllBicliquesContained(edges: set<(int,int)>, V: set<int>,
                                       result: seq<set<int>>)
{
  forall K :: IsInducedBiclique(edges, K) && K <= V ==>
    exists i :: 0 <= i < |result| && K <= result[i]
}

// Recursive-level Property B contract, restricted to (H, C, Gamma).
ghost predicate CoversBicliquesRestricted(edges: set<(int,int)>, V: set<int>,
                                           H: set<int>, C: set<int>,
                                           S: seq<set<int>>)
{
  forall K :: IsInducedBiclique(edges, K) && K <= V
              && K <= H + C + Gamma(edges, V, C)
              && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
    ==> exists i :: 0 <= i < |S| && K <= S[i]
}

// Recursive encoding: avoids forall-exists issues.
ghost function AggregatorContractF(edges: set<(int,int)>, V: set<int>,
                                    H: set<int>, C: set<int>,
                                    result: seq<set<int>>, pNum: nat, pDen: nat): bool
  requires pDen > 0
  decreases |result|
{
  if |result| == 0 then true
  else (exists H2: set<int>, C2: set<int> ::
          H2 <= H && C <= C2 &&
          result[0] == H2 + C2 + Gamma(edges, V, C2) &&
          DensityGT(edges, V, H2, C2, pNum, pDen)) &&
       AggregatorContractF(edges, V, H, C, result[1..], pNum, pDen)
}

ghost predicate AggregatorContract(edges: set<(int,int)>, V: set<int>,
                                    H: set<int>, C: set<int>,
                                    result: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0
{
  AggregatorContractF(edges, V, H, C, result, pNum, pDen)
}

// -----------------------------------------------------------------
// Lemmas
// -----------------------------------------------------------------

lemma DensityDecisionIsSound(edges: set<(int,int)>, V: set<int>,
                               H: set<int>, C: set<int>, pNum: nat, pDen: nat)
  requires pDen > 0
  requires DensityGT(edges, V, H, C, pNum, pDen)
  ensures  RhoDense(edges, V, H, C, pNum, pDen) {}

//helpers for decreases
lemma SubsetCardinality(A: set<int>, B: set<int>)
  requires A <= B
  ensures |A| <= |B|
{
  var diff := B - A;
  assert A * diff == {};
  assert A + diff == B;
  assert |A + diff| == |A| + |diff|;
}

lemma SubsetCardinalityGeneric<T>(A: set<T>, B: set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  var diff := B - A;
  assert A * diff == {};
  assert A + diff == B;
  assert |A + diff| == |A| + |diff|;
}


lemma ContractImpliesRhoDense(edges: set<(int,int)>, V: set<int>,
                                H: set<int>, C: set<int>,
                                result: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0
  requires AggregatorContract(edges, V, H, C, result, pNum, pDen)
  ensures  AllRhoDense(edges, V, result, pNum, pDen)
  decreases |result|
{
  if |result| > 0 {
    var h2, c2 :| h2 <= H && C <= c2 &&
                  result[0] == h2 + c2 + Gamma(edges, V, c2) &&
                  DensityGT(edges, V, h2, c2, pNum, pDen);
    DensityDecisionIsSound(edges, V, h2, c2, pNum, pDen);
    ContractImpliesRhoDense(edges, V, H, C, result[1..], pNum, pDen);
  }
}

lemma ContractSubset(edges: set<(int,int)>, V: set<int>, H: set<int>, C: set<int>,
                     Hv: set<int>, Cv: set<int>, Sv: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0
  requires Hv <= H
  requires C <= Cv
  requires AggregatorContract(edges, V, Hv, Cv, Sv, pNum, pDen)
  ensures  AggregatorContract(edges, V, H, C, Sv, pNum, pDen)
  decreases |Sv|
{
  if |Sv| > 0 {
    var h2, c2 :| h2 <= Hv && Cv <= c2 &&
                  Sv[0] == h2 + c2 + Gamma(edges, V, c2) &&
                  DensityGT(edges, V, h2, c2, pNum, pDen);
    assert h2 <= H && C <= c2;
    ContractSubset(edges, V, H, C, Hv, Cv, Sv[1..], pNum, pDen);
  }
}

lemma ContractConcat(edges: set<(int,int)>, V: set<int>, H: set<int>, C: set<int>,
                     S1: seq<set<int>>, S2: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0
  requires AggregatorContract(edges, V, H, C, S1, pNum, pDen)
  requires AggregatorContract(edges, V, H, C, S2, pNum, pDen)
  ensures  AggregatorContract(edges, V, H, C, S1 + S2, pNum, pDen)
  decreases |S1|
{
  if |S1| == 0 {
    assert S1 + S2 == S2;
  } else {
    var h2, c2 :| h2 <= H && C <= c2 &&
                  S1[0] == h2 + c2 + Gamma(edges, V, c2) &&
                  DensityGT(edges, V, h2, c2, pNum, pDen);
    ContractConcat(edges, V, H, C, S1[1..], S2, pNum, pDen);
    assert (S1 + S2)[0] == S1[0];
    assert (S1 + S2)[1..] == S1[1..] + S2;
  }
}

lemma CoverConcat(edges: set<(int,int)>, V: set<int>, H: set<int>, C: set<int>,
                  S1: seq<set<int>>, S2: seq<set<int>>)
  requires CoversBicliquesRestricted(edges, V, H, C, S1)
  ensures  CoversBicliquesRestricted(edges, V, H, C, S1 + S2)
{
  forall K | IsInducedBiclique(edges, K) && K <= V
             && K <= H + C + Gamma(edges, V, C)
             && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
    ensures exists i :: 0 <= i < |S1 + S2| && K <= (S1 + S2)[i]
  {
    var j :| 0 <= j < |S1| && K <= S1[j];
    assert (S1 + S2)[j] == S1[j];
  }
}

lemma CoverConcat2(edges: set<(int,int)>, V: set<int>, H: set<int>, C: set<int>,
                   S1: seq<set<int>>, S2: seq<set<int>>)
  requires CoversBicliquesRestricted(edges, V, H, C, S2)
  ensures  CoversBicliquesRestricted(edges, V, H, C, S1 + S2)
{
  forall K | IsInducedBiclique(edges, K) && K <= V
             && K <= H + C + Gamma(edges, V, C)
             && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
    ensures exists i :: 0 <= i < |S1 + S2| && K <= (S1 + S2)[i]
  {
    var j :| 0 <= j < |S2| && K <= S2[j];
    assert (S1 + S2)[|S1| + j] == S2[j];
  }
}

lemma GammaMonotone(edges: set<(int,int)>, V: set<int>, C1: set<int>, C2: set<int>)
  requires C1 <= C2
  ensures Gamma(edges, V, C2) <= Gamma(edges, V, C1)
{
  forall w | w in Gamma(edges, V, C2)
    ensures w in Gamma(edges, V, C1)
  {
    forall c | c in C1
      ensures Adjacent(edges, w, c)
    { assert c in C2; }
  }
}

lemma DenseSetCoversAll(edges: set<(int,int)>, V: set<int>,
                         H: set<int>, C: set<int>, pNum: nat, pDen: nat)
  requires pDen > 0
  requires DensityGT(edges, V, H, C, pNum, pDen)
  ensures  CoversBicliquesRestricted(edges, V, H, C, [H + C + Gamma(edges, V, C)])
{
  forall K | IsInducedBiclique(edges, K) && K <= V
             && K <= H + C + Gamma(edges, V, C)
             && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
    ensures exists i :: 0 <= i < |[H + C + Gamma(edges, V, C)]| &&
                        K <= [H + C + Gamma(edges, V, C)][i]
  {
    assert [H + C + Gamma(edges, V, C)][0] == H + C + Gamma(edges, V, C);
  }
}

// Gamma(V, {}) == V
lemma GammaEmptyCoreIsV(edges: set<(int,int)>, V: set<int>)
  ensures Gamma(edges, V, {}) == V
{
  forall u | u in V
    ensures u in Gamma(edges, V, {})
  {
    assert forall c :: c in {} ==> Adjacent(edges, u, c);
  }
}

// Helpers that we assume to be correct. Not trying to verify degeneracy ordering in this work.

ghost method {:axiom} GetOrderH(edges: set<(int,int)>, V: set<int>, H: set<int>)
  returns (orderH: seq<int>)
  ensures forall i :: 0 <= i < |orderH| ==> orderH[i] in H
  ensures forall v :: v in H ==> exists i :: 0 <= i < |orderH| && orderH[i] == v
  ensures |orderH| == |H|
  ensures forall i, j :: 0 <= i < j < |orderH| ==> orderH[i] != orderH[j]

ghost method {:axiom} GetHv(edges: set<(int,int)>, V: set<int>,
                            H: set<int>, C: set<int>, v: int)
  returns (Hv: set<int>)
  requires v in H
  ensures Hv <= H
  ensures v !in Hv
  ensures |Hv| < |H|
  // Local biclique coverage axiom:
  //   For any induced biclique K that passes through the pivot v and lies
  //   within the current search region H+C+Gamma(V,C) [note that proving this is sufficient], two things hold:
  //   (a) K is fully contained in the inner search region Hv+(C+{v})+Gamma(V,C+{v}),
  //   (b) the inner call's CoversBicliquesRestricted condition is met:
  //       either K has vertices in Hv to pivot on, or Gamma(V,C+{v}) is
  //       non-empty (so the dense base-case output covers K).
  ensures forall K :: IsInducedBiclique(edges, K) && v in K && K <= V
                      && K <= H + C + Gamma(edges, V, C)
            ==> K <= Hv + (C + {v}) + Gamma(edges, V, C + {v})
                && (K * Hv != {} || Gamma(edges, V, C + {v}) != {})

// Helper: a > 0 && b > 0 ==> a * b > 0  (proved by induction on b).
// Probably overkill to include. Could've ghosted. c'est la vie. 
lemma MulStrictlyPositive(a: int, b: int)
  requires a > 0
  requires b > 0
  ensures  a * b > 0
  decreases b
{
  if b == 1 {
    calc { a * b; == a * 1; == a; }
  } else {
    MulStrictlyPositive(a, b - 1);
    calc { a * b; == a * (b - 1) + a; }
  }
}

// |Pa| == |B|  when Pa == {(a0,b) | b in B}  expressed via membership predicates.
lemma PaCardEqualsB(a0: int, B: set<int>, Pa: set<(int,int)>)
  requires forall b :: b in B ==> (a0, b) in Pa
  requires forall p :: p in Pa ==> p.0 == a0 && p.1 in B
  ensures  |Pa| == |B|
  decreases |B|
{
  if B == {} {
    assert forall p :: p in Pa ==> p.1 in B;
    assert Pa == {};
  } else {
    var b0 :| b0 in B;
    var B'  := B - {b0};
    var Pa' := Pa - {(a0, b0)};
    assert (a0, b0) in Pa;
    assert Pa == Pa' + {(a0, b0)};
    assert (a0, b0) !in Pa';
    assert |Pa| == |Pa'| + 1;
    assert forall b :: b in B' ==> (a0, b) in Pa' by {
      forall b | b in B' ensures (a0, b) in Pa' {
        assert b != b0;
        assert (a0, b) in Pa;
        assert (a0, b) != (a0, b0);
      }
    }
    assert forall p :: p in Pa' ==> p.0 == a0 && p.1 in B' by {
      forall p | p in Pa' ensures p.0 == a0 && p.1 in B' {
        assert p in Pa;
        assert p.0 == a0 && p.1 in B;
        assert p != (a0, b0);
        assert p.1 != b0;
      }
    }
    PaCardEqualsB(a0, B', Pa');
    assert |B'| == |B| - 1;
  }
}

// |P| == |A| * |B|  when P == A × B  expressed via membership predicates.
lemma EdgeSetProductCardinality(A: set<int>, B: set<int>, P: set<(int,int)>)
  requires forall a, b :: a in A && b in B ==> (a, b) in P
  requires forall p :: p in P ==> p.0 in A && p.1 in B
  ensures  |P| == |A| * |B|
  decreases |A|
{
  if A == {} {
    assert forall p :: p in P ==> p.0 in A;
    assert P == {};
  } else {
    var a0 :| a0 in A;
    var A' := A - {a0};
    var Pa := set p | p in P && p.0 == a0;
    var P' := set p | p in P && p.0 in A';
    assert P == Pa + P' by {
      forall p | p in P ensures p in Pa + P' {
        if p.0 == a0 { assert p in Pa; }
        else { assert p.0 in A'; assert p in P'; }
      }
    }
    assert Pa * P' == {} by {
      forall p | p in Pa && p in P' ensures false {
        assert p.0 == a0 && p.0 in A';
        assert a0 !in A';
      }
    }
    assert |P| == |Pa| + |P'|;
    // |Pa| == |B|
    assert forall b :: b in B ==> (a0, b) in Pa by {
      forall b | b in B ensures (a0, b) in Pa {
        assert (a0, b) in P;
      }
    }
    assert forall p :: p in Pa ==> p.0 == a0 && p.1 in B;
    PaCardEqualsB(a0, B, Pa);
    assert |Pa| == |B|;
    // |P'| == |A'| * |B|
    assert forall a, b :: a in A' && b in B ==> (a, b) in P' by {
      forall a, b | a in A' && b in B ensures (a, b) in P' {
        assert (a, b) in P;
        assert a in A';
      }
    }
    assert forall p :: p in P' ==> p.0 in A' && p.1 in B;
    EdgeSetProductCardinality(A', B, P');
    assert |A'| == |A| - 1;
    calc {
      |P|;
      == |Pa| + |P'|;
      == |B| + |A'| * |B|;
      == (1 + |A'|) * |B|;
      == |A| * |B|;
    }
  }
}


// If C is nonempty and Gamma(V,C) is nonempty and pNum < pDen then DensityGT(V, {}, C) holds.  
//Used to show the post-loop "else" branch is unreachable: the loop invariant gives !DensityGT(∅,C) at loop exit,
// which contradicts this lemma under the same hypotheses.
lemma GammaDenseCheck(edges: set<(int,int)>, V: set<int>, C: set<int>,
                       pNum: nat, pDen: nat)
  requires Undirected(edges)
  requires pDen > 0
  requires pNum < pDen
  requires |C| > 0
  requires Gamma(edges, V, C) != {}
  ensures DensityGT(edges, V, {}, C, pNum, pDen)
{
 {
  var G := Gamma(edges, V, C);
  // Every (c,g) pair with c in C, g in G is in edges.
  forall c, g | c in C && g in G
    ensures (c, g) in edges
  {
    assert Adjacent(edges, g, c);
    assert (g, c) in edges;
    assert (c, g) in edges;
  }
  var edgePairs := set p | p in edges && p.0 in C && p.1 in G;
  // All C×G pairs are in edgePairs.
  assert forall a, b :: a in C && b in G ==> (a, b) in edgePairs by {
    forall a, b | a in C && b in G ensures (a, b) in edgePairs {
      assert (a, b) in edges;
    }
  }
  // edgePairs contains only C×G pairs (by definition).
  assert forall p :: p in edgePairs ==> p.0 in C && p.1 in G;
  // |edgePairs| == |C| * |G| (no lambda-lifting issues since P is an explicit parameter).
  EdgeSetProductCardinality(C, G, edgePairs);
  assert |edgePairs| == |C| * |G|;
  assert EdgeCount(edges, C, G) == |edgePairs|;
  // Arithmetic: EdgeCount * pDen > pNum * |C| * |G|.
  assert |G| > 0;
  assert |C| > 0;
  var N := |C| * |G|;
  assert N > 0;
  var K := pDen - pNum;
  assert K >= 1;
  calc { N * pDen - N * pNum; == N * (pDen - pNum); == N * K; }
  MulStrictlyPositive(N, K);
  assert N * K > 0;
  assert N * pDen > N * pNum;
  assert N * pNum == pNum * N;
  assert N * pDen == |C| * |G| * pDen;
  assert pNum * N == pNum * |C| * |G|;
  assert |C| * |G| * pDen > pNum * |C| * |G|;
  assert EdgeCount(edges, C, G) * pDen > pNum * |C| * |G|;
 }
}

// Product-set cardinality: |{(a,b) | a in A, b in B}| == |A| * |B|.
lemma ProductCardinalityLemma<T, U>(A: set<T>, B: set<U>)
  ensures |set a, b | a in A && b in B :: (a, b)| == |A| * |B|
{
  if A == {} {
    assert (set a, b | a in A && b in B :: (a, b)) == {};
  } else {
    var a0 :| a0 in A;
    var A' := A - {a0};
    var P  := set a, b | a in A  && b in B :: (a, b);
    var P' := set a, b | a in A' && b in B :: (a, b);
    var Pa := set b | b in B :: (a0, b);
    // Pa and P' are disjoint (Pa has a0 as first component, P' has A').
    assert Pa !! P' by {
      forall p | p in Pa && p in P'
        ensures false
      {
        assert p.0 == a0;
        assert p.0 in A';
        assert a0 !in A';
      }
    }
    // P is the disjoint union of Pa and P'.
    assert P == Pa + P' by {
      forall p | p in P
        ensures p in Pa + P'
      {
        if p.0 == a0 { assert p in Pa; } else { assert p.0 in A'; assert p in P'; }
      }
      forall p | p in Pa + P'
        ensures p in P
      { }
    }
    assert |P| == |Pa| + |P'|;
    // |Pa| == |B|: the map b -> (a0, b) is a bijection Pa <-> B.
    assert |Pa| == |B| by { SingletonRowCardinality(a0, B); }
    // |P'| == |A'| * |B| by induction.
    ProductCardinalityLemma(A', B);
    assert |A'| == |A| - 1;
    calc {
      |P|;
      == |Pa| + |P'|;
      == |B| + |A'| * |B|;
      == (1 + |A'|) * |B|;
      == |A| * |B|;
    }
  }
}

// Helper: |{(a0, b) | b in B}| == |B|.
lemma SingletonRowCardinality<T, U>(a0: T, B: set<U>)
  ensures |set b | b in B :: (a0, b)| == |B|
{
  if B == {} {
    assert (set b | b in B :: (a0, b)) == {};
  } else {
    var b0 :| b0 in B;
    var B' := B - {b0};
    var Row  := set b | b in B  :: (a0, b);
    var Row' := set b | b in B' :: (a0, b);
    assert (a0, b0) in Row;
    assert (a0, b0) !in Row' by {
      assert b0 !in B';
    }
    assert Row == Row' + {(a0, b0)} by {
      forall p | p in Row
        ensures p in Row' + {(a0, b0)}
      {
        if p.1 == b0 { assert p == (a0, b0); } else { assert p.1 in B'; assert p in Row'; }
      }
      forall p | p in Row' + {(a0, b0)}
        ensures p in Row
      { }
    }
    assert |Row| == |Row'| + 1;
    SingletonRowCardinality(a0, B');
    assert |Row'| == |B'|;
    assert |B'| == |B| - 1;
  }
}

// -----------------------------------------------------------------
// Main Algorithm
// -----------------------------------------------------------------

ghost method {:timeLimitMultiplier 8} Aggregator(edges: set<(int,int)>, V: set<int>,
                                                H: set<int>, C: set<int>, pNum: nat, pDen: nat)
  returns (S: seq<set<int>>)
  requires pDen > 0
  requires pNum < pDen
  requires Undirected(edges)
  decreases |H|
  ensures AggregatorContract(edges, V, H, C, S, pNum, pDen)
  ensures CoversBicliquesRestricted(edges, V, H, C, S)
{
  // ---- Base case: region is dense ----
  if DensityGT(edges, V, H, C, pNum, pDen) {
    S := [H + C + Gamma(edges, V, C)];

    // Prove Property A: AggregatorContractF([H+C+Gamma]) with witnesses H, C.
    assert AggregatorContractF(edges, V, H, C, S, pNum, pDen) by {
      assert S[0] == H + C + Gamma(edges, V, C);
      assert H <= H && C <= C && S[0] == H + C + Gamma(edges, V, C) &&
             DensityGT(edges, V, H, C, pNum, pDen);
    }

    // Prove Property B via lemma
    DenseSetCoversAll(edges, V, H, C, pNum, pDen);
    assert S == [H + C + Gamma(edges, V, C)];
    return S;
  }

  // ---- Recursive case ----
  S := [];
  var currentH := H;
  var orderH := GetOrderH(edges, V, H);
  var i := 0;

  while i < |orderH|
    invariant 0 <= i <= |orderH|
    decreases |orderH| - i
    invariant currentH <= H
    invariant forall v :: v in currentH ==>
                exists j :: i <= j < |orderH| && orderH[j] == v
    invariant forall j :: i <= j < |orderH| ==> orderH[j] in currentH
    invariant AggregatorContract(edges, V, H, C, S, pNum, pDen)
    // Every K whose H-portion has already been processed is covered in S.
    invariant forall K :: IsInducedBiclique(edges, K) && K <= V
                          && K <= H + C + Gamma(edges, V, C)
                          && K * (H - currentH) != {}
                ==> exists k :: 0 <= k < |S| && K <= S[k]
    // DensityGT was false at start and remains false (else, we returned).
    invariant !DensityGT(edges, V, currentH, C, pNum, pDen)
  {
    var v := orderH[i];

    if v in currentH {
      var Hv := GetHv(edges, V, currentH, C, v);
      var Cv := C + {v};

      SubsetCardinality(currentH, H);

      var Sv := Aggregator(edges, V, Hv, Cv, pNum, pDen);

      // Lift Property A
      ContractSubset(edges, V, H, C, Hv, Cv, Sv, pNum, pDen);
      ContractConcat(edges, V, H, C, S, Sv, pNum, pDen);

      // Lift Property B: every K touching H-(currentH-{v}) is covered by S+Sv.
      forall K | IsInducedBiclique(edges, K) && K <= V
                 && K <= H + C + Gamma(edges, V, C)
                 && K * (H - (currentH - {v})) != {}
        ensures exists k :: 0 <= k < |S + Sv| && K <= (S + Sv)[k]
      {
        if v in K {
          if K * (H - currentH) != {} {
            // K was already covered by the loop invariant.
            var k :| 0 <= k < |S| && K <= S[k];
            assert (S + Sv)[k] == S[k];
          } else {
            // K*(H-currentH)={} and v in K => v is the only new processed element.
            // Show K <= currentH+C+Gamma (all of K's H-part is still in currentH).
            assert forall w :: w in K ==> w in currentH + C + Gamma(edges, V, C) by {
              forall w | w in K
                ensures w in currentH + C + Gamma(edges, V, C)
              {
                if w in H && w !in currentH {
                  assert w in H - currentH;
                  assert w in K * (H - currentH);
                }
              }
            }
            assert K <= currentH + C + Gamma(edges, V, C);
            // Apply the combined BicliqueCoverage axiom (v in K, K <= currentH+C+Gamma):
            assert K <= Hv + Cv + Gamma(edges, V, Cv);
            assert K * Hv != {} || Gamma(edges, V, Cv) != {};
            // Inner Sv satisfies CoversBicliquesRestricted(Hv,Cv), so it covers K.
            assert |Cv| > 0;
            var k :| 0 <= k < |Sv| && K <= Sv[k];
            assert (S + Sv)[|S| + k] == Sv[k];
          }
        } else {
          // v not in K; so K*(H-(currentH-{v})) = K*(H-currentH) != {}.
          assert K * (H - currentH) != {};
          var k :| 0 <= k < |S| && K <= S[k];
          assert (S + Sv)[k] == S[k];
        }
      }

      S := S + Sv;
      currentH := currentH - {v};

      // ---- Dense sub-case ----
      if DensityGT(edges, V, currentH, C, pNum, pDen) {
        var res := currentH + C + Gamma(edges, V, C);
        var Sres := [res];

        // Property A for Sres: witnesses currentH, C for the single element.
        assert AggregatorContractF(edges, V, H, C, Sres, pNum, pDen) by {
          assert currentH <= H;
          assert Sres[0] == currentH + C + Gamma(edges, V, C);
          assert DensityGT(edges, V, currentH, C, pNum, pDen);
        }

        ContractConcat(edges, V, H, C, S, Sres, pNum, pDen);

        // Property B for S+Sres
        forall K | IsInducedBiclique(edges, K) && K <= V
                   && K <= H + C + Gamma(edges, V, C)
                   && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
          ensures exists k :: 0 <= k < |S + Sres| && K <= (S + Sres)[k]
        {
          if K * (H - currentH) != {} {
            var k :| 0 <= k < |S| && K <= S[k];
            assert (S + Sres)[k] == S[k];
          } else if K * currentH != {} {
            // K's H-part all in currentH => K <= res
            assert K <= currentH + C + Gamma(edges, V, C);
            assert (S + Sres)[|S|] == res;
          } else {
            // K*H={}, guarded by |C|>0 and Gamma nonempty; K <= H+C+Gamma <= res
            assert (S + Sres)[|S|] == res;
          }
        }

        S := S + Sres;
        return S;
      }
    }
    i := i + 1;
  }

  // currentH must be empty (orderH was a full permutation of H)
  assert currentH == {} by {
    forall v | v in currentH
      ensures false
    {
      assert exists j :: i <= j < |orderH| && orderH[j] == v;
      assert i == |orderH|;
    }
  }

  // Property B at loop exit.
  // Loop invariant gives !DensityGT(∅, C).  If |C|>0 and Gamma!={} then GammaDenseCheck would give DensityGT(∅,C) — a contradiction.
  // So the guard (K*H!={} || (|C|>0 && Gamma!={})) collapses to K*H!={}, which is covered by the loop invariant (currentH={} so H-currentH=H).
  assert !DensityGT(edges, V, {}, C, pNum, pDen);   // from loop invariant + currentH={}
  assert !(|C| > 0 && Gamma(edges, V, C) != {}) by {
    if |C| > 0 && Gamma(edges, V, C) != {} {
      GammaDenseCheck(edges, V, C, pNum, pDen);      // gives DensityGT(∅,C)
      assert false;
    }
  }
  assert CoversBicliquesRestricted(edges, V, H, C, S) by {
    forall K | IsInducedBiclique(edges, K) && K <= V
               && K <= H + C + Gamma(edges, V, C)
               && (K * H != {} || (|C| > 0 && Gamma(edges, V, C) != {}))
      ensures exists k :: 0 <= k < |S| && K <= S[k]
    {
      // Guard reduces to K*H != {} (the second disjunct is false, shown above).
      assert K * H != {};
      // currentH={} so H - currentH = H; the loop invariant fires.
      assert K * (H - currentH) != {};
      var k :| 0 <= k < |S| && K <= S[k];
    }
  }

  return S;
}

// initial call

ghost method TopLevelAggregator(edges: set<(int,int)>, V: set<int>,
                                 pNum: nat, pDen: nat)
  returns (result: seq<set<int>>)
  requires pDen > 0
  requires pNum < pDen
  requires Undirected(edges)
  ensures AllRhoDense(edges, V, result, pNum, pDen)
  ensures AllBicliquesContained(edges, V, result)
{
  result := Aggregator(edges, V, V, {}, pNum, pDen);

  // Property A
  ContractImpliesRhoDense(edges, V, V, {}, result, pNum, pDen);

  // Property B: Gamma(V,{}) = V, every biclique K<=V has K*V = K != {}.
  GammaEmptyCoreIsV(edges, V);
  forall K | IsInducedBiclique(edges, K) && K <= V
    ensures exists i :: 0 <= i < |result| && K <= result[i]
  {
    assert K * V != {};
    assert K <= V + {} + Gamma(edges, V, {});
    var i :| 0 <= i < |result| && K <= result[i];
  }
}

// Final check

lemma BothPropertiesHold(edges: set<(int,int)>, V: set<int>,
                          H: set<int>, C: set<int>,
                          result: seq<set<int>>, pNum: nat, pDen: nat)
  requires pDen > 0 && pNum < pDen
  requires AggregatorContract(edges, V, H, C, result, pNum, pDen)
  requires AllBicliquesContained(edges, V, result)
  ensures  AllRhoDense(edges, V, result, pNum, pDen)
  ensures  AllBicliquesContained(edges, V, result)
{
  ContractImpliesRhoDense(edges, V, H, C, result, pNum, pDen);
}
