module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Choose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.DualIncl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatCountAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatticeIsDiscreteGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps
import Mathlib.Algebra.Module.StablyFree.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchIneq

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.PackLem

section

@[expose] public section

noncomputable section

open MeasureTheory Metric Module

namespace PI.UnitaryGroupMassFormula.LCG

def matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖matVec A‖ = hsN A := by
  rw [EuclideanSpace.norm_eq, hsN, Formalism.REAL.hs, Fintype.sum_prod_type]
  rfl

theorem matVec_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : matVec (A - B) = matVec A - matVec B := by
  ext ij
  simp [matVec]

theorem finrank_matSpace (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, sq]

theorem lattice_packLem : PackLem := by
  intro ι _ N R ρ hρ hR T hT hsep
  classical
  let W := EuclideanSpace ℂ (Fin N × Fin N)
  let μ : Measure W := Measure.addHaar
  let ν : Measure (ι → W) := Measure.pi fun _ => μ
  let B : (ι → Matrix (Fin N) (Fin N) ℂ) → Set (ι → W) :=
    fun p => Set.univ.pi fun v => ball (matVec (p v)) (ρ v / 2)
  let Big : Set (ι → W) := Set.univ.pi fun v => ball (0 : W) (R v + ρ v / 2)
  have hdisj : (T : Set (ι → Matrix (Fin N) (Fin N) ℂ)).PairwiseDisjoint B := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨v, hv⟩ := hsep p hp q hq hpq
    have h1 := (Set.mem_univ_pi.1 hzp) v
    have h2 := (Set.mem_univ_pi.1 hzq) v
    rw [mem_ball] at h1 h2
    have h3 : dist (matVec (p v)) (matVec (q v)) < ρ v := by
      calc dist (matVec (p v)) (matVec (q v)) ≤ dist (matVec (p v)) (z v) + dist (z v) (matVec (q v)) :=
            dist_triangle _ _ _
        _ < ρ v / 2 + ρ v / 2 := by rw [dist_comm] at h1; exact add_lt_add h1 h2
        _ = ρ v := by ring
    rw [dist_eq_norm, ← matVec_sub, norm_matVec] at h3
    linarith
  have hmeas : ∀ p ∈ T, MeasurableSet (B p) := fun p _ =>
    MeasurableSet.univ_pi fun v => measurableSet_ball
  have hsub : (⋃ p ∈ T, B p) ⊆ Big := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Set.mem_univ_pi.2 fun v => ?_
    have h1 := (Set.mem_univ_pi.1 hz) v
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    have h2 : ‖matVec (p v)‖ ≤ R v := by rw [norm_matVec]; exact hT p hp v
    calc ‖z v‖ = ‖(z v - matVec (p v)) + matVec (p v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z v - matVec (p v)‖ + ‖matVec (p v)‖ := norm_add_le _ _
      _ < ρ v / 2 + R v := by linarith
      _ = R v + ρ v / 2 := by ring
  have key : ∑ p ∈ T, ν (B p) ≤ ν Big := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  set d := finrank ℝ W with hd
  set c := μ (ball (0 : W) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ (0 : W) one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have hB : ∀ p, ν (B p) = ∏ v, ENNReal.ofReal ((ρ v / 2) ^ d) * c := by
    intro p
    simp only [ν, B, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v])
  have hBig : ν Big = ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c := by
    simp only [ν, Big, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v, hR v])
  simp only [hB, Finset.sum_const, nsmul_eq_mul] at key
  rw [hBig] at key
  have hfin : ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c ≠ ⊤ :=
    ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have key' := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_prod] at key'
  simp only [ENNReal.toReal_mul] at key'
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hpos : ∀ v, 0 < ρ v / 2 := fun v => by linarith [hρ v]
  simp only [fun v => ENNReal.toReal_ofReal (pow_nonneg (hpos v).le d),
    fun v => ENNReal.toReal_ofReal (pow_nonneg (add_pos_of_nonneg_of_pos (hR v) (hpos v)).le d)] at key'
  have hprodpos : 0 < ∏ v, (ρ v / 2) ^ d * c.toReal :=
    Finset.prod_pos fun v _ => mul_pos (pow_pos (hpos v) d) hc'
  rw [← le_div_iff₀ hprodpos, ← Finset.prod_div_distrib] at key'
  have hdN : d = 2 * N ^ 2 := finrank_matSpace N
  calc (T.card : ℝ) ≤ ∏ v, (R v + ρ v / 2) ^ d * c.toReal / ((ρ v / 2) ^ d * c.toReal) := key'
    _ = ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_div_mul_right _ _ hc'.ne', ← div_pow, hdN]
      congr 1
      have := hρ v
      field_simp

end PI.UnitaryGroupMassFormula.LCG

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SublatticeOfLattice

section

@[expose] public section

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem sublattice_of_lattice : LatSub := by
  intro I x u u' hu hu'
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu hu' ⊢
  have h : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((u - u') i)) =
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) -
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u' i)) := by
    funext i
    simp [map_sub]
  rw [h, Matrix.mulVec_sub]
  exact Submodule.sub_mem _ hu hu'

theorem lattice_map_image : LatMap := by
  intro I x y γ g hγ hK u hu
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu ⊢
  have h1 : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      I.fmat γ.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    funext i
    rw [hγ]
    exact RingHom.map_mulVec _ _ _ i
  have hK' : ∀ v, v ∈ I.Lf ↔ I.fmat (x⁻¹ * γ * y).2 *ᵥ v ∈ I.Lf := hK
  have hk := (hK' (I.fmat y.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i))).1 hu
  rw [h1]
  convert hk using 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Formalism.MainNotions.S.AutInst.fmat, Prod.snd_mul, Prod.snd_inv]
  push_cast
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)),
    Matrix.mul_one]

theorem norm_positive : NPos := by
  intro I x h
  by_contra hn
  have hn0 : I.n = 0 := by omega
  have hE : IsEmpty (PI.LatCountG.Sub I x) := by
    constructor
    intro s
    have hj := s.j_pos
    apply s.b_ind.ne_zero ⟨0, by omega⟩
    funext i
    exact absurd i.2 (by omega)
  have h0 : PI.LatCountG.tau1 I x = 0 := by
    unfold PI.LatCountG.tau1
    rw [Real.iInf_of_isEmpty]
    exact min_eq_right (by norm_num)
  linarith

theorem card_places_bound : CardPl := by
  intro I
  haveI : NumberField.IsTotallyReal I.F := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  have h3 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (K := I.F)
  show _ = Module.finrank ℚ I.F
  omega

end PI.UnitaryGroupMassFormula.LCG
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.NormProd

section

@[expose] public section

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.LSC.NormProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem algebraMap_norm_eq (hc : Formalism.BasicNotions.CMData F E) (m : E) :
    algebraMap F E (Algebra.norm F m) = m * star m := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  have hfix : ∀ r : F, starRingAut (algebraMap F E r) = algebraMap F E r := fun r =>
    (hc.fixed _).mpr ⟨r, rfl⟩
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) hfix
  have hσ : ∀ a, σ a = star a := fun _ => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    have hall : ∀ a : E, a ∈ (algebraMap F E).range := fun a => by
      rw [← hc.fixed, ← hσ, ← h]; rfl
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      ext a; simpa [Algebra.mem_bot] using hall a
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    rw [hc.deg2] at h1; norm_num at h1
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hc.deg2]
    exact (Fintype.card_le_of_injective (fun e : E ≃ₐ[F] E => (e : E →ₐ[F] E))
      (fun a b h => AlgEquiv.coe_algHom_injective h)).trans AlgHom.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_univ _
  have hcard : Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
    rw [hc.deg2]; omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, Finset.card_pair hne]; omega)).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

end PI.UnitaryGroupMassFormula.LSC.NormProd

namespace PI.UnitaryGroupMassFormula.LSC

open PI.UnitaryGroupMassFormula.LSC.NormProd

theorem norm_product_formula : NormProd := by
  intro I m
  letI := I.fF; letI := I.nF; letI := I.fE; letI := I.nE; letI := I.sE; letI := I.aFE
  have hc := I.cm
  set N := Algebra.norm I.F m with hN
  have hv : ∀ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = v N := by
    intro v
    have h1 : I.φ v (m * star m) = v.embedding N := by
      rw [← algebraMap_norm_eq hc m, I.φ_over]
    rw [map_mul, hc.cmUnram.2.1, Complex.mul_conj] at h1
    rw [← InfinitePlace.norm_embedding_eq, ← h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  have hmult : ∀ v : InfinitePlace I.F, v.mult = 1 := fun v =>
    InfinitePlace.mult_isReal ⟨v, hc.totReal.isReal v⟩
  have := InfinitePlace.prod_eq_abs_norm N
  simp only [hmult, pow_one] at this
  rw [this, hN, Algebra.norm_norm, Rat.cast_abs]

end PI.UnitaryGroupMassFormula.LSC
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LCG

theorem latCountAll_of_steps (hB : BoxBound) (hP : PackLem) (hD : DualIncl) (hCh : Choose) (hA : ArchIneq)
    (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of hB lattice_map_image sublattice_of_lattice
    (separation_of_points lattice_is_discrete_group hD hCh (hAP hA) hI PI.UnitaryGroupMassFormula.LSC.norm_product_formula PI.UnitaryGroupMassFormula.LSC.determinant_monotone card_places_bound)
    hP norm_positive card_places_bound

theorem latCountAll_of_open (hD : DualIncl) (hCh : Choose) (hAP : ArchPlaceOf) (hI : IndexIneq) :
    PI.LatCountG.LatCountAll :=
  latCountAll_of_steps box_lattice_point_bound lattice_packLem hD hCh archimedean_inequality hAP hI

theorem latCountAll_of_open2 (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open dual_lattice_inclusion choice_of_generators hAP hI

theorem latCountAll_of_index (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open2 archimedean_place_exists hI

theorem latCountAll_of_idx (hD2 : DetIdx) (hIO : IndexOf) : PI.LatCountG.LatCountAll :=
  latCountAll_of_index (hIO dual_index_formula hD2)

end PI.UnitaryGroupMassFormula.LCG
end
end
end
