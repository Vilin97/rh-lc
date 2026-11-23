module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialEvalCompat
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoVanish

open HomogeneousLocalization MvPolynomial

variable {K : Type} [Field K] {N : ℕ}

theorem away_mk_zero {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    (h0 : (0 : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n 0 h0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

theorem away_mk_add {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (n • 1)) (hb : b ∈ grK K N (n • 1))
    (hab : a + b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a + b) hab = Away.mk (grK K N) hx n a ha + Away.mk (grK K N) hx n b hb := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]

theorem away_mk_mul {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) {k m n : ℕ} (hn : k + m = n)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (k • 1)) (hb : b ∈ grK K N (m • 1))
    (hab : a * b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a * b) hab = Away.mk (grK K N) hx k a ha * Away.mk (grK K N) hx m b hb := by
  subst hn
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add x k m)

theorem chart_zero {R : Type} [CommRing R] {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1)
    (φ : Away (grK K N) x →+* R) (S : Set (MvPolynomial (Fin (N + 1)) K))
    (hS : ∀ f ∈ S, ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), φ (Away.mk (grK K N) hx d f hf) = 0)
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ Ideal.span S) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
  have hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ),
      (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1) := by
    intro q n
    simpa using (DirectSum.decompose (grK K N) q n).2
  have hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro n f hf h
    have h0 : f = 0 := by simpa using h
    subst h0
    rw [away_mk_zero, map_zero]
  have hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K),
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) (p + q) n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro p q ihp ihq n f hf h
    have h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) +
        (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) := by
      rw [h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    subst h'
    rw [away_mk_add hx n (hmem p n) (hmem q n), map_add (f := _), ihp n _ _ rfl, ihq n _ _ rfl, add_zero]
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, hd, h0⟩ := hS p hp
    intro n f hf h
    have hd' : p ∈ grK K N d := by simpa using hd
    by_cases hnd : n = d
    · subst hnd
      have : f = p := h.trans (DirectSum.decompose_of_mem_same _ hd')
      subst this
      exact h0
    · have h1 : f = 0 := h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))
      subst h1
      rw [away_mk_zero, map_zero]
  | zero => exact hzero
  | add p q _ _ ihp ihq => exact hadd p q ihp ihq
  | smul a p _ ih =>
    induction a using DirectSum.Decomposition.inductionOn (grK K N) with
    | zero => simpa using hzero
    | @homogeneous k m =>
      intro n f hf h
      rw [smul_eq_mul] at h
      by_cases hk : k ≤ n
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk] at h
        subst h
        have hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1) := by simpa using m.2
        rw [away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul,
          ih (n - k) _ _ rfl, mul_zero]
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk] at h
        subst h
        rw [away_mk_zero, map_zero]
    | add a b iha ihb =>
      rw [add_smul]
      exact hadd _ _ iha ihb

theorem evV_res {X : Scheme.{0}} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K) {V W : X.Opens}
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : W ≤ V) (y : Away (grK K N) g) :
    resO h (evV i g V hV y) = evV i g W (h.trans hV) y := by
  have := Scheme.Hom.appLE_map i hV (homOfLE h).op
  simp only [evV]
  exact congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))

theorem evV_awayMap {X : Scheme.{0}} (i : X ⟶ PSpace K N) {a b c : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hb : b ∈ grK K N m) (hc : c = a * b) {W : X.Opens} (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) c)
    (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) a) (y : Away (grK K N) a) :
    evV i c W hW (awayMap (grK K N) hb hc y) = evV i a W hW' y := by
  have h1 := Proj.awayMap_awayToSection (grK K N) hb hc
  have h2 := Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op
  have h3 : (Proj.awayToSection (grK K N) c).hom (awayMap (grK K N) hb hc y) =
      ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom
        ((Proj.awayToSection (grK K N) a).hom y) := congr($(h1).hom y)
  simp only [evV, RingHom.comp_apply]
  rw [h3]
  exact congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))

theorem exists_chart (p : PSpace K N) : ∃ j, p ∈ Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) := by
  have h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)
    change f ∈ Ideal.span _
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hf' : f ∈ grK K N n := hf
    have := ((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)
    simp only [map_zero] at this
    omega
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))

theorem ratio_eq {g x f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ} (hg : g ∈ grK K N e) (hx : x ∈ grK K N 1)
    (hf : f ∈ grK K N (s • e)) (hf1 : f ∈ grK K N ((s • e) • 1)) (hxs : x ^ (s • e) ∈ grK K N (s • e)) :
    awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s f hf) =
      awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s (x ^ (s • e)) hxs) *
        awayMap (grK K N) hg (mul_comm g x) (Away.mk (grK K N) hx (s • e) f hf1) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.GeoVanish


open GlobalTheory.CompanionTheory.GeoVanish in
theorem GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e) (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e)), f ∈ homIdeal i → ∀ (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g), evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
  intro K _ X N i g e he hg s f hf hfI V hV
  have hf1 : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0 := by
    intro j
    refine chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1
      (DirectSum.decompose_of_mem_same _ hf).symm
    rintro p ⟨d, hp, h⟩
    exact ⟨d, hp, h j⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V
    (fun j => homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    obtain ⟨j, hj⟩ := exists_chart (i p)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
    exact And.intro hp hj
  · intro j
    set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef
    have hx : x ∈ grK K N 1 := xv_mem K N j
    set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef
    have hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g := inf_le_left.trans hV
    have hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x := inf_le_right
    have hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x) := by
      rw [Proj.basicOpen_mul]
      exact fun p hp => And.intro (hWg hp) (hWx hp)
    have hxs : x ^ (s • e) ∈ grK K N (s • e) := by
      simpa using SetLike.pow_mem_graded (s • e) hx
    have h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0 := by
      rw [← evV_res i x le_rfl hWx, key j, map_zero]
    have h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
      rw [← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul,
        evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]
    change resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0
    rw [map_zero, evV_res i g hV inf_le_left]
    exact h1
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo


open MvPolynomial in
theorem exists_monic_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (y : Fin m → MvPolynomial σ K)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (a : MvPolynomial σ K) :
    ∃ (s : ℕ) (C : ℕ → MvPolynomial (Fin m) K), 0 < s ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (C l) * a ^ l ∈ I := by
  by_cases htop : I = ⊤
  · exact ⟨1, 0, one_pos, by simp [htop]⟩
  haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB
  haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)
  have hq : (p * Polynomial.X).Monic := hp.mul Polynomial.monic_X
  have hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a)
      (p * Polynomial.X) = 0 := by
    rw [Polynomial.eval₂_mul, hroot, zero_mul]
  have hdeg : 0 < (p * Polynomial.X).natDegree := by
    rw [hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]
    omega
  generalize p * Polynomial.X = q at hq hroot' hdeg
  have hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I) := by
    intro l
    have hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈
        (aeval (fun k => Ideal.Quotient.mk I (y k)) :
          MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff l).2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    have := MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y
      (Ideal.Quotient.mkₐ K I) c
    simpa using this
  choose C hC using hlift
  refine ⟨q.natDegree, C, hdeg, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range,
    Finset.sum_range_succ, map_add, map_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hC, map_pow]
    rfl
  · simp [hq.coeff_natDegree]


open MvPolynomial in
theorem homogeneousComponent_aeval_mul {K σ : Type} [Field K] {m e : ℕ} (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (C : MvPolynomial (Fin m) K) (r t : ℕ) (b : MvPolynomial σ K) (hb : b.IsHomogeneous t) :
    homogeneousComponent (e * r + t) (aeval y C * b) = aeval y (homogeneousComponent r C) * b := by
  have key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) =
      if r' = r then aeval y (homogeneousComponent r C) * b else 0 := by
    intro r'
    have h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t) :=
      ((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    by_cases hr : r' = r
    · subst hr
      simp
    · have hne : e * r' + t ≠ e * r + t := fun h' =>
        hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))
      rw [if_neg hne.symm, if_neg hr]
  conv_lhs => rw [← sum_homogeneousComponent C]

  rw [map_sum, Finset.sum_mul, map_sum]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]
    simp


open MvPolynomial in
theorem exists_hom_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (e : ℕ) (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (w : ℕ) (a : MvPolynomial σ K) (ha : a.IsHomogeneous (e * w)) :
    ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (c l) * a ^ l ∈ I := by
  obtain ⟨s, C, hs, hmem⟩ := exists_monic_relation I y hfin a
  refine ⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs,
    fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hcomp := hI _ hmem (e * w * s)

  rw [map_add (f := _), map_sum] at hcomp
  convert hcomp using 2
  · have h := ha.pow s
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    simp
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have hdeg : e * w * s = e * ((s - l) * w) + e * w * l := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]

end GlobalTheory.CompanionTheory.Geo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFinite

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoInteg

theorem away_val_mk {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (n : ℕ) (x : MvPolynomial (Fin (N + 1)) K) (hx : x ∈ grK K N (n • D)) :
    (HomogeneousLocalization.Away.mk (grK K N) hg n x hx).val =
      algebraMap _ (Localization.Away g) x * (IsLocalization.Away.invSelf g : Localization.Away g) ^ n := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  have h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1 :=
    IsLocalization.Away.mul_invSelf g
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]

theorem away_relation {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (r • D))
    (c : ℕ → MvPolynomial (Fin (N + 1)) K) (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D))
    (F : MvPolynomial (Fin (N + 1)) K) (hF : F ∈ grK K N ((s * r) • D))
    (hFe : F = f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l) :
    HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ s +
      ∑ l ∈ Finset.range s, HomogeneousLocalization.Away.mk (grK K N) hg _ (c l) (hc l) *
        HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ l =
      HomogeneousLocalization.Away.mk (grK K N) hg _ F hF := by
  have val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g),
      (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val := fun t u =>
    map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_mul, val_sum, away_val_mk]
  rw [hFe]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm s r]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have : s * r = (s - l) * r + r * l := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [this, pow_add, mul_pow, ← pow_mul]
    ring

theorem rel_mem {K : Type} [Field K] {N : ℕ} {D : ℕ} (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f ∈ grK K N (r • D)) (c : ℕ → MvPolynomial (Fin (N + 1)) K)
    (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D)) :
    f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l ∈ grK K N ((s * r) • D) := by
  have hf' : f.IsHomogeneous (r • D) := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  refine add_mem ?_ (sum_mem fun l hl => ?_)
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    convert hf'.pow s using 1
    simp only [smul_eq_mul]
    ring
  · have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    rw [MvPolynomial.mem_homogeneousSubmodule]
    convert ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    ring

theorem isIntegral_torusS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  intro K _ X N d e i y hy V hV he q hq hfin S hS ht
  letI := (strV q V).toAlgebra
  intro a
  have hg := yS_mem y hy S
  obtain ⟨r, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grK K N) hg a
  by_cases hS0 : S.card = 0
  ·
    have hf0 : f.IsHomogeneous 0 := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      simpa [hS0] using this
    have hfC : f = MvPolynomial.C (AddMonoidAlgebra.coeff f 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)
    have hc : (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card) := by
      rw [hS0, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_C _ _
    have hmem := GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc
    have hfe : MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K) = f := by
      rw [MvPolynomial.aeval_C]
      exact hfC.symm
    have heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf := by
      simp only [hfe]
    rw [heq] at hmem
    exact isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)
  · have hD : 0 < S.card * e := Nat.mul_pos (Nat.pos_of_ne_zero hS0) he
    have hfh : f.IsHomogeneous (e * (r * S.card)) := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      convert this using 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨s, c, -, hc, hrel⟩ := GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh
    have hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card) := fun l => by
      rw [mul_assoc]
      exact hc l
    have hcm := fun l => aeval_mem y hy S (c l) (hc' l)
    have hF := rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm
    have hid := away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl
    have hzero := GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS
    rw [← hid] at hzero

    rw [map_add (f := _), map_sum] at hzero
    simp only [map_mul, map_pow] at hzero
    have hco := fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)
    refine ⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s,
      Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      rw [← Polynomial.mem_degreeLT]
      refine Submodule.sum_mem _ fun l hl => ?_
      rw [Polynomial.mem_degreeLT]
      refine (Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_
      exact_mod_cast Finset.mem_range.1 hl
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hzero

end GlobalTheory.CompanionTheory.GeoInteg
end
end
end
