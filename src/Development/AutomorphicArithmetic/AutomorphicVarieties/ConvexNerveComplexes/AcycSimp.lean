module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Convex.Hull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Sublevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Perturb
public import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveCompact
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.VertFinite

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.vert_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ K : Set E, IsCompact K → K ⊆ poly q → {h | h ∈ K ∧ IsVert q h}.Finite := by
  intro E Y _ _ q hq K hK hKp
  choose S hSf hSU using fun x (hx : x ∈ K) => hq x (hKp hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => {h' : E | ∀ y ∉ S x hx, 1 < q y h'})
    (fun x hx => hSU x hx)
  have hfin : (⋃ x ∈ (t : Set K), S x.1 x.2).Finite :=
    t.finite_toSet.biUnion fun x _ => hSf x.1 x.2
  refine Set.Finite.of_finite_image (f := fun v : E => {y : Y | q y v = 1}) ?_ ?_
  · refine hfin.finite_subsets.subset ?_
    rintro _ ⟨v, ⟨hvK, hvV⟩, rfl⟩
    have hv := ht hvK
    simp only [Set.mem_iUnion] at hv
    obtain ⟨x, hxt, hvx⟩ := hv
    show {y : Y | q y v = 1} ⊆ _
    intro y hy
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨x, hxt, ?_⟩
    by_contra hyS
    have h1 := (hvx : ∀ y ∉ S x.1 x.2, 1 < q y v) y hyS
    simp only [Set.mem_setOf_eq] at hy
    linarith
  · rintro v ⟨_, hvV⟩ w ⟨_, hwV⟩ hvw
    have key : w - v = 0 := by
      refine hvV.2 (w - v) fun y hy => ?_
      have hy' : y ∈ {y : Y | q y w = 1} := by
        have e : {y : Y | q y v = 1} = {y : Y | q y w = 1} := hvw
        rw [← e]
        exact hy
      simp only [Set.mem_setOf_eq] at hy'
      simp [map_sub, hy, hy']
    exact (sub_eq_zero.1 key).symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.ConeFinite

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.cone_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ s : Set (E →L[ℝ] ℝ), s.Finite → s ⊆ posDual T → {v : Vert q | (convexHull ℝ s ∩ normalCone q v.1).Nonempty}.Finite := by
  intro E Y _ _ _ q T hg s hs hsT
  obtain ⟨h0, hh0⟩ := hg.nonempty
  let K : Set E := ⋃ x ∈ s, {h | h ∈ poly q ∧ x h ≤ x h0}
  have hK : IsCompact K := hs.isCompact_biUnion fun x hx => sublevel hg x (hsT hx) (x h0)
  have hKp : K ⊆ poly q := by
    intro h hh
    simp only [K, Set.mem_iUnion] at hh
    obtain ⟨x, _, hp, _⟩ := hh
    exact hp
  refine ((vert_finite hg.locFin K hK hKp).preimage Subtype.val_injective.injOn).subset ?_
  rintro v ⟨z, hzs, hzv⟩
  refine ⟨?_, v.2⟩
  simp only [K, Set.mem_iUnion]
  by_contra hno
  push_neg at hno
  have hconv : Convex ℝ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    refine convex_halfSpace_gt ?_ 0
    exact ⟨fun f g => rfl, fun c f => rfl⟩
  have hsub : s ⊆ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    intro x hx
    have hlt : x h0 < x v.1 := by
      by_contra hle
      exact hno x hx ⟨v.2.1, not_lt.mp hle⟩
    simp only [Set.mem_setOf_eq, map_sub]
    linarith
  have hz := convexHull_min hsub hconv hzs
  have hz2 := hzv h0 hh0
  simp only [Set.mem_setOf_eq, map_sub] at hz
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.DualConvex

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.dual_convex : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Y → E →L[ℝ] ℝ) (T : Set E), Convex ℝ (posDual T) ∧ ∀ h : E, IsClosed (normalCone q h) ∧ Convex ℝ (normalCone q h) := by
  intro E Y _ _ q T
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · intro x hx y hy a b ha hb hab
    simp only [posDual, Set.mem_setOf_eq] at hx hy ⊢
    intro k hk hk0
    have h1 := hx k hk hk0
    have h2 := hy k hk hk0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha'
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
    · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
  · have e : normalCone q h = ⋂ h' ∈ poly q, {x : E →L[ℝ] ℝ | x h ≤ x h'} := by
      ext x
      simp [normalCone]
    rw [e]
    exact isClosed_biInter fun h' _ =>
      isClosed_le (ContinuousLinearMap.apply ℝ ℝ h).continuous (ContinuousLinearMap.apply ℝ ℝ h').continuous
  · intro x hx y hy a b ha hb hab
    simp only [normalCone, Set.mem_setOf_eq] at hx hy ⊢
    intro h' hh'
    have h1 := hx h' hh'
    have h2 := hy h' hh'
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.ExistsVert

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.exists_vert :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ x ∈ posDual T, ∃ v : Vert q, x ∈ normalCone q v.1 := by
  intro E Y _ _ _ q T hG x hx
  obtain ⟨h0, hh0⟩ := hG.nonempty
  have hK := sublevel hG x hx (x h0)
  obtain ⟨hm, hmK, hmin⟩ := hK.exists_isMinOn ⟨h0, hh0, le_rfl⟩ x.continuous.continuousOn
  have hglob : ∀ h' ∈ poly q, x hm ≤ x h' := by
    intro h' hh'
    by_cases hle : x h' ≤ x h0
    · exact hmin ⟨hh', hle⟩
    · have : x hm ≤ x h0 := hmK.2
      linarith [not_le.mp hle]
  have hF := sublevel hG x hx (x hm)
  obtain ⟨e, he⟩ := hF.extremePoints_nonempty ⟨hm, hmK.1, le_rfl⟩
  rw [mem_extremePoints] at he
  obtain ⟨⟨hep, hex⟩, hext⟩ := he
  refine ⟨⟨e, hep, ?_⟩, ?_⟩
  · intro k hk
    obtain ⟨ε, hε, hs⟩ := perturb hG.locFin e hep k hk
    have ha := hs ε (by rw [abs_of_pos hε])
    have hb := hs (-ε) (by rw [abs_neg, abs_of_pos hε])
    have hxa := hglob _ ha
    have hxb := hglob _ hb
    simp only [map_add (f := _), map_smul, smul_eq_mul] at hxa hxb
    have hmem1 : e + ε • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨ha, by simp only [map_add (f := _), map_smul, smul_eq_mul]; linarith⟩
    have hmem2 : e + (-ε) • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨hb, by simp only [map_add (f := _), map_smul, smul_eq_mul]; linarith⟩
    have hseg : e ∈ openSegment ℝ (e + ε • k) (e + (-ε) • k) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have heq := (hext _ hmem1 _ hmem2 hseg).1
    have hzero : ε • k = 0 := by
      have := congrArg (fun w => w - e) heq
      simpa using this
    exact (smul_eq_zero.mp hzero).resolve_left hε.ne'
  · simp only [normalCone, Set.mem_setOf_eq]
    intro h' hh'
    exact le_trans hex (hglob h' hh')
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycDirected

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_directed :
    ∀ {I : Type} (S : ∀ n, Set (Fin n → I)), (∀ (n : ℕ) (s : Finset (Fin n → I)), (↑s : Set (Fin n → I)) ⊆ S n → ∃ S' : ∀ k, Set (Fin k → I), (∀ k, S' k ⊆ S k) ∧ (↑s : Set (Fin n → I)) ⊆ S' n ∧ Acyc S') → Acyc S := by
  intro I S h
  refine ⟨fun c hc => ?_, fun n c hc h0 => ?_⟩
  · obtain ⟨S', hS, hs, hA⟩ := h 0 c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.1 c ((Finsupp.mem_supported ℤ c).2 hs)
    exact ⟨b, Finsupp.supported_mono (hS 1) hb, e⟩
  · obtain ⟨S', hS, hs, hA⟩ := h (n + 1) c.support ((Finsupp.mem_supported ℤ c).1 hc)
    obtain ⟨b, hb, e⟩ := hA.2 n c ((Finsupp.mem_supported ℤ c).2 hs) h0
    exact ⟨b, Finsupp.supported_mono (hS (n + 2)) hb, e⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveConvex

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_convex :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → (∀ s : Set F, s.Finite → s ⊆ X → {i | (convexHull ℝ s ∩ A i).Nonempty}.Finite) → (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) := by
  intro I F _ _ X A hX hne hcl hcv hfin hcov
  apply acyc_directed
  intro n s hs
  have hw : ∀ t ∈ (s : Set (Fin n → I)), ∃ x ∈ X, ∀ j, x ∈ A (t j) := fun t ht => hs ht
  choose! w hwX hwA using hw
  obtain ⟨x0, hx0⟩ := hne
  let P : Set F := insert x0 (w '' (s : Set (Fin n → I)))
  have hPfin : P.Finite := (s.finite_toSet.image w).insert x0
  have hPX : P ⊆ X := by
    intro x hx
    rcases hx with rfl | ⟨t, ht, rfl⟩
    · exact hx0
    · exact hwX t ht
  let K : Set F := convexHull ℝ P
  have hKX : K ⊆ X := convexHull_min hPX hX
  have hKc : IsCompact K := hPfin.isCompact_convexHull (𝕜 := ℝ)
  refine ⟨nerve K A, ?_, ?_, ?_⟩
  · intro k t ht
    obtain ⟨x, hx, hxA⟩ := ht
    exact ⟨x, hKX hx, hxA⟩
  · intro t ht
    refine ⟨w t, subset_convexHull ℝ P (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩), hwA t ht⟩
  · apply nerve_compact K A hKc (convex_convexHull ℝ P)
      ⟨x0, subset_convexHull ℝ P (Set.mem_insert _ _)⟩ hcl hcv (hfin P hPfin hPX)
    intro x hx
    exact hcov x (hKX hx)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_simp : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → FaceClosed (simp q T) ∧ simp q T 0 = univ ∧ Acyc (simp q T) := by
  intro E Y _ _ _ q T hG
  refine ⟨UpperTheory.V.ConeExtensionAcyclic.nerve_faceClosed _ _, ?_, ?_⟩
  · ext t
    simp only [UpperTheory.V.ConeExtensionAcyclic.simp, UpperTheory.V.ConeExtensionAcyclic.nerve, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hG.pos
    exact ⟨x, hx, fun j => j.elim0⟩
  · exact UpperTheory.V.ConeExtensionAcyclic.nerve_convex _ _ (UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).1 hG.pos
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).1)
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).2)
      (UpperTheory.V.ConeExtensionAcyclic.cone_finite hG) (UpperTheory.V.ConeExtensionAcyclic.exists_vert hG)
end
end
