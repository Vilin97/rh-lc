module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarInfiniteGLLtTopOfInfiniteGLHaarMeasureLtTopStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Separation.Connected
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTop

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem covol_le_of_mul_left (Γ Γ' : Set (MatInf E j)) (h : MatInf E j) (hh : 0 < detNorm E j h)
    (A B : Set (MatInf E j)) (hAB : ∀ x ∈ A, h * x ∈ B)
    (hΓ : ∀ δ ∈ Γ', ∃ δ₀ ∈ Γ, ∀ x, h * (δ₀ * x) = δ * (h * x)) :
    covol Γ (haarGL E j) A ≤ covol Γ' (haarGL E j) B := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hmeas : Measurable (fun g : MatInf E j => h * g) :=
    (GlobalTheory.MeanDual.measurePreserving_mul_left E j h hh).measurable
  refine iInf_le_of_le ((fun g => h * g) ⁻¹' D') (iInf_le_of_le (hmeas hD') (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨δ, hδ, hx'⟩ := hc (h * x) (hAB x hx)
    obtain ⟨δ₀, hδ₀, H⟩ := hΓ δ hδ
    refine ⟨δ₀, hδ₀, ?_⟩
    show h * (δ₀ * x) ∈ D'
    rw [H]; exact hx'
  · rw [← Measure.map_apply hmeas hD', GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq E j h hh]

def scal (r : ℝ) : MatInf E j := fun _ a b => if a = b then (r : ℂ) else 0

theorem of_scal (r : ℝ) (w : InfinitePlace E) :
    Matrix.of (scal E j r w) = (r : ℂ) • (1 : Matrix (Fin j) (Fin j) ℂ) := by
  ext a b
  simp [scal, Matrix.one_apply]

theorem scal_mul_comm (r : ℝ) (δ x : MatInf E j) : scal E j r * (δ * x) = δ * (scal E j r * x) := by
  apply matInf_ext
  intro w
  simp only [of_mul, of_scal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

theorem detNorm_scal (r : ℝ) (hr : 0 < r) :
    detNorm E j (scal E j r) = (r ^ (2 * j)) ^ Fintype.card (InfinitePlace E) := by
  unfold detNorm
  simp only [of_scal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, ← pow_mul, mul_comm]

theorem exists_scal (hj : 1 ≤ j) (c : ℝ) (hc : 0 < c) : ∃ r : ℝ, 0 < r ∧ detNorm E j (scal E j r) = c := by
  have hN : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  refine ⟨c ^ (((2 * j * Fintype.card (InfinitePlace E) : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [detNorm_scal E j _ (Real.rpow_pos_of_pos hc _), ← pow_mul]
  exact Real.rpow_inv_natCast_pow hc.le (by positivity)

def slab (c : ℝ) : Set (MatInf E j) := {x | c ≤ detNorm E j x ∧ detNorm E j x < c * Real.exp 1}

theorem covol_slab_le (hj : 1 ≤ j) (Λ : Submodule (𝓞 E) (Fin j → E)) (c : ℝ) (hc : 0 < c) :
    covol (autGL E j Λ) (haarGL E j) (slab E j c) ≤
      covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} := by
  obtain ⟨r, hr, hd⟩ := exists_scal E j hj c⁻¹ (inv_pos.2 hc)
  refine covol_le_of_mul_left E j _ _ (scal E j r) (hd ▸ inv_pos.2 hc) _ _ ?_
    (fun δ hδ => ⟨δ, hδ, fun x => scal_mul_comm E j r δ x⟩)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq, detNorm_mul, hd]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact h1
  · rw [inv_mul_eq_div, div_lt_iff₀ hc, mul_comm]; exact h2

theorem covol_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ≤
      covol (autGL E j Λ') (haarGL E j) (slab E j (detNorm E j (embInf E j γ))) := by
  refine covol_le_of_mul_left E j _ _ (embInf E j γ) (detNorm_embInf E j γ) _ _ ?_ ?_
  · rintro x ⟨h1, h2⟩
    simp only [slab, Set.mem_setOf_eq, detNorm_mul]
    have hp := detNorm_embInf E j γ
    exact ⟨le_mul_of_one_le_right hp.le h1, mul_lt_mul_of_pos_left h2 hp⟩
  · intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
    refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x => ?_⟩
    apply matInf_ext
    intro w
    simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
    have := embInf_inv_mul E j γ⁻¹ w
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]

theorem glVol_lt_top (hE : IsTotallyComplex E) : ∀ j : ℕ, 1 ≤ j → glVol E j < ⊤ := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.NormOneVol.glVol_one E hE]; exact ENNReal.ofReal_lt_top
    · have h := ih hn
      have hs := GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (n + 1) (by omega) (by simpa using h)
      rw [hs]
      simp only [Nat.add_sub_cancel] at h ⊢
      exact ENNReal.mul_lt_top h ENNReal.ofReal_lt_top

end GlobalTheory.SlabFinVol


open GlobalTheory.FlagMeas GlobalTheory.MeanDual in
theorem GlobalTheory.SlabFinVol.covol_unitSlab_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  have hfin := GlobalTheory.SlabFinVol.glVol_lt_top E hE j hj
  let R : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} → Prop :=
    fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1
  have hle : _ ≤ glVol E j := ENNReal.le_tsum (Quot.mk R ⟨Λ, hΛ⟩)
  have hrel := Quot.eqvGen_exact (Quot.out_eq (Quot.mk R ⟨Λ, hΛ⟩))
  have key : ∀ a b, Relation.EqvGen R a b →
      ∃ γ : GL (Fin j) E, Carries E j γ a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel x y h => exact h
    | refl x => exact ⟨1, fun y => by simp⟩
    | symm x y _ ih => obtain ⟨γ, h⟩ := ih; exact ⟨γ⁻¹, h.inv⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨γ, h⟩ := ih1; obtain ⟨δ, h'⟩ := ih2; exact ⟨δ * γ, h'.mul h⟩
  obtain ⟨γ, hγ⟩ := key _ _ hrel
  exact lt_of_le_of_lt ((covol_le_of_carries E j hγ.inv).trans
    (GlobalTheory.SlabFinVol.covol_slab_le E j hj _ _ (detNorm_embInf E j _))) (lt_of_le_of_lt hle hfin)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTopStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  letI : Submodule.IsFullLattice E Λ := hΛ
  apply GlobalTheory.SlabFinVol.covol_unitSlab_lt_top <;> first | assumption | infer_instance
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinity

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.GLInfReduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def entries (y : Matrix (Fin a) (Fin a) (Cinf E)) : GlobalTheory.FlagMeas.MatInf E a := fun w i k => y i k w

def dn (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∏ w, ‖(y.det) w‖ ^ 2

theorem detNorm_entries (y : Matrix (Fin a) (Fin a) (Cinf E)) :
    GlobalTheory.FlagMeas.detNorm E a (entries y) = dn y := by
  unfold GlobalTheory.FlagMeas.detNorm dn
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of (entries y w) = (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix y := by
    ext i k; rfl
  rw [this, ← RingHom.map_det]; rfl

theorem entries_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : entries (g * y) = entries g * entries y := by
  funext w i k
  change (g * y) i k w = (Matrix.of (entries g w) * Matrix.of (entries y w)) i k
  simp [Matrix.mul_apply, Finset.sum_apply, entries]

theorem dn_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : dn (g * y) = dn g * dn y := by
  simp [dn, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]

theorem dn_pos (y : GL (Fin a) (Cinf E)) : 0 < dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := by
  refine Finset.prod_pos fun w _ => ?_
  have h : (y : Matrix (Fin a) (Fin a) (Cinf E)).det * ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h' := congrFun h w
  have hne : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 := left_ne_zero_of_mul_eq_one h'
  positivity

end GlobalTheory.GLInfReduction


open GlobalTheory.GLInfReduction in
theorem GlobalTheory.GLInfReduction.exists_cover_of_finite_measure (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)) (hΛ : Submodule.IsFullLattice E Λ)
    [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure] :
    ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E,
      (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧
      ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨Set.univ, ?_, fun y => ⟨1, by simp, 0, trivial⟩⟩
    haveI : Subsingleton (GL (Fin 0) (Cinf E)) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Finite (GL (Fin 0) (Cinf E)) := Finite.of_subsingleton
    exact isCompact_univ.measure_lt_top
  set r := Fintype.card (InfinitePlace E) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set N : ℕ := 2 * a * r with hN_def
  have hN : 0 < N := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'

  have hslab := GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top E inferInstance a ha Λ (by
    letI := hΛ
    infer_instance)
  simp only [GlobalTheory.FlagMeas.covol, iInf_lt_iff] at hslab
  obtain ⟨D, hDm, hcov, hDlt⟩ := hslab
  have hD' := GlobalTheory.T.haar_infiniteGL_lt_top_of_infiniteGLHaarMeasure_lt_top E a ν D hDm hDlt
  set S : Set (GL (Fin a) (Cinf E)) := {y | entries (y : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D} with hS
  have hS' : ν S < ⊤ := hD'

  let c : ℝ → GL (Fin a) (Cinf E) := fun t => GeneralLinearGroup.map (pInf E) (splitCentre E a t)
  have hc_val : ∀ t : ℝ, (c t : Matrix (Fin a) (Fin a) (Cinf E)) =
      Matrix.scalar (Fin a) (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := by
    intro t
    simp only [c, splitCentre, pInf_infGL]
    rfl
  have hc_dn : ∀ t : ℝ, dn (c t : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (N * t) := by
    intro t
    rw [hc_val, dn]
    simp only [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Pi.pow_apply, norm_pow, Complex.norm_exp_ofReal]
    rw [← hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hN_def]
    congr 1; push_cast; ring
  have hcomm : ∀ t g, c t * g = g * c t := by
    intro t g
    have := congrArg (GeneralLinearGroup.map (pInf E)) (splitCentre_comm (E := E) (a := a) t (infGL E a g))
    simpa [map_mul] using this
  have hcint : ∀ n : ℤ, GeneralLinearGroup.map (pInf E) (splitCentre E a 1 ^ n) = c n := by
    intro n; simp only [c, splitCentre_intCast]
  refine ⟨⋃ k ∈ Finset.range N, (fun h => c (-(k : ℝ) / N) * h) ⁻¹' S, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    rw [measure_preimage_mul]
    exact hS'
  · intro y
    set L := Real.log (dn (y : Matrix (Fin a) (Fin a) (Cinf E)))
    have hL : Real.exp L = dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := Real.exp_log (dn_pos y)
    set m := ⌊L⌋
    set q := m / (N : ℤ)
    set ρ := m % (N : ℤ)
    have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hρN : ρ < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    have hm : ρ + N * q = m := by simp only [ρ, q]; rw [Int.emod_def]; ring
    set k := ρ.toNat
    have hk : (k : ℤ) = ρ := Int.toNat_of_nonneg hρ0
    have hkN : k < N := by omega
    set x := c (-(k : ℝ) / N) * (c ((-q : ℤ) : ℝ) * y)
    have hx : dn (x : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (L - m) := by
      simp only [x, Units.val_mul, dn_mul, hc_dn, ← hL, ← Real.exp_add]
      congr 1
      have hmR : (ρ : ℝ) + N * q = m := by exact_mod_cast hm
      have hkR : (k : ℝ) = ρ := by exact_mod_cast hk
      rw [← hmR, hkR]; push_cast; field_simp; ring
    have hxS : 1 ≤ GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
        GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) < Real.exp 1 := by
      rw [detNorm_entries, hx]
      constructor
      · exact Real.one_le_exp (by linarith [Int.floor_le L])
      · exact Real.exp_lt_exp.2 (by linarith [Int.lt_floor_add_one L])
    obtain ⟨g, ⟨γ, hγΛ, hgγ⟩, hgD⟩ := hcov _ hxS
    refine ⟨γ, hγΛ, -q, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, hkN, ?_⟩
    set R := GeneralLinearGroup.map (pInf E) (ratGL E a γ)
    have hR : entries (R : Matrix (Fin a) (Fin a) (Cinf E)) = g := by
      funext w i j
      rw [hgγ w i j]
      exact pInf_algebraMap (γ i j) w
    have e1 : c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) = R * x := by
      rw [map_mul, hcint, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc, mul_assoc]
    change entries ((c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) :
      GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D
    rw [e1, Units.val_mul, entries_mul, hR]
    exact hgD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinityStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.exists_finite_measure_reduction_domain_infinity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)), Submodule.IsFullLattice E Λ → ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure], ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E, (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧ ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  first | exact @GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | exact GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | (intros; apply GlobalTheory.GLInfReduction.exists_cover_of_finite_measure <;> assumption)
end
end
