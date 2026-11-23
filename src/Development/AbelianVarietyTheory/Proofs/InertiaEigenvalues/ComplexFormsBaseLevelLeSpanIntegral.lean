module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportTermSubset

section

@[expose] public section

noncomputable section

open Formalism.IndefR

namespace GlobalTheory.LawTrace

variable {G Γ W : Type} [Group G] [Group Γ] [AddCommGroup W] [Module ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)


open Classical in
def term (y x : G) (P : W) (γ : Γ) : W :=
  if h : (ι γ * y)⁻¹ * x ∈ J then ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • ρ γ P else 0

def tr (y : G) (P : W) : G → W := fun x => ∑ᶠ γ, term ι ρ J χ y x P γ

variable {ι ρ J χ}

theorem support_term_subset (y x : G) (P : W) :
    Function.support (term ι ρ J χ y x P) ⊆ {γ | (ι γ * y)⁻¹ * x ∈ J} := by
  intro γ hγ
  by_contra h
  exact hγ (by unfold term; exact dif_neg (show ¬ ((ι γ * y)⁻¹ * x ∈ J) from h))

theorem finite_cond {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) : {γ | (ι γ * y)⁻¹ * x ∈ J}.Finite := by
  rcases Set.eq_empty_or_nonempty {γ | (ι γ * y)⁻¹ * x ∈ J} with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
    refine (hs.image fun s => γ₀ * s).subset fun γ hγ => ⟨γ₀⁻¹ * γ, ?_, by simp⟩
    change γ₀⁻¹ * γ ∈ Bridge.stab ι J y
    rw [Bridge.mem_stab]
    have h1 := J.mul_mem h₀ (J.inv_mem (show (ι γ * y)⁻¹ * x ∈ J from hγ))
    convert h1 using 1
    simp [mul_assoc]

theorem support_term_finite {y : G} (hf : Finite (Bridge.stab ι J y)) (x : G) (P : W) :
    (Function.support (term ι ρ J χ y x P)).Finite :=
  (finite_cond hf x).subset (support_term_subset y x P)

theorem term_mul (y x : G) (P : W) (γ₀ γ : Γ) (k : J) :
    term ι ρ J χ y (ι γ₀ * x * k) P (γ₀ * γ) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (term ι ρ J χ y x P γ) := by
  have e : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) = (ι γ * y)⁻¹ * x * k := by
    simp [mul_assoc]
  unfold term
  by_cases h : (ι γ * y)⁻¹ * x ∈ J
  · have h' : (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
    rw [dite_eq_left h', dite_eq_left h]
    have ek : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
    rw [ek, map_mul, map_mul, Units.val_mul, map_smul, smul_smul, mul_comm, Module.End.mul_apply]
  · have h' : ¬ (ι (γ₀ * γ) * y)⁻¹ * (ι γ₀ * x * k) ∈ J := by
      rw [e]; intro h2; exact h (by simpa using J.mul_mem h2 (J.inv_mem k.2))
    rw [dif_neg h', dif_neg h, map_zero, smul_zero]

theorem tr_law {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (γ₀ : Γ) (x : G) (k : J) :
    tr ι ρ J χ y P (ι γ₀ * x * k) = ((χ k : ℂˣ) : ℂ) • ρ γ₀ (tr ι ρ J χ y P x) := by
  unfold tr
  rw [← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  simp only [Equiv.coe_mulLeft, term_mul]
  let L : W →ₗ[ℂ] W := ((χ k : ℂˣ) : ℂ) • ρ γ₀
  change ∑ᶠ γ, L (term ι ρ J χ y x P γ) = L (∑ᶠ γ, term ι ρ J χ y x P γ)
  exact (map_finsum L (support_term_finite hf x P)).symm

theorem mem_lawForms_tr {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) :
    tr ι ρ J χ y P ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ :=
  GlobalTheory.ExportSeries.mem_lawForms.2 fun γ x k => tr_law hf P γ x k

theorem tr_add {y : G} (hf : Finite (Bridge.stab ι J y)) (P Q : W) :
    tr ι ρ J χ y (P + Q) = tr ι ρ J χ y P + tr ι ρ J χ y Q := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (P + Q) γ = term ι ρ J χ y x P γ + term ι ρ J χ y x Q γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_add]
  simp only [tr, Pi.add_apply, e]
  exact finsum_add_distrib (support_term_finite hf x P) (support_term_finite hf x Q)

theorem tr_smul (y : G) (a : ℂ) (P : W) : tr ι ρ J χ y (a • P) = a • tr ι ρ J χ y P := by
  funext x
  have e : ∀ γ, term ι ρ J χ y x (a • P) γ = a • term ι ρ J χ y x P γ := fun γ => by
    unfold term; split_ifs <;> simp [smul_comm a]
  simp only [tr, Pi.smul_apply, e]
  exact (smul_finsum a _).symm

theorem tr_zero (y : G) : tr ι ρ J χ y (0 : W) = 0 := by
  simpa using tr_smul (ι := ι) (ρ := ρ) (χ := χ) y (0 : ℂ) (0 : W)

theorem tr_mem {R : Type} [Semiring R] [Module R W] {y : G} (hf : Finite (Bridge.stab ι J y)) (P : W) (x : G)
    (M : Submodule R W) (hM : ∀ γ, (ι γ * y)⁻¹ * x ∈ J → term ι ρ J χ y x P γ ∈ M) : tr ι ρ J χ y P x ∈ M := by
  unfold tr
  rw [finsum_eq_sum _ (support_term_finite hf x P)]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h := support_term_subset y x P ((Set.Finite.mem_toFinset _).1 hγ)
  exact hM γ h

theorem tr_self {y : G} (hf : Finite (Bridge.stab ι J y)) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    tr ι ρ J χ y (F y) y = (Nat.card (Bridge.stab ι J y) : ℂ) • F y := by
  classical
  have e : ∀ γ, term ι ρ J χ y y (F y) γ = if γ ∈ Bridge.stab ι J y then F y else 0 := fun γ => by
    unfold term
    have hc : (ι γ * y)⁻¹ * y ∈ J ↔ γ ∈ Bridge.stab ι J y := by
      rw [Bridge.mem_stab, ← J.inv_mem_iff]
      simp [mul_assoc]
    by_cases h : (ι γ * y)⁻¹ * y ∈ J
    · rw [dite_eq_left h, if_pos (hc.1 h)]
      have := GlobalTheory.ExportSeries.mem_lawForms.1 hF γ y ⟨_, h⟩
      rw [show ι γ * y * ((ι γ * y)⁻¹ * y) = y by group] at this
      exact this.symm
    · rw [dif_neg h, if_neg fun h' => h (hc.2 h')]
  unfold tr
  simp only [e]
  have hs : ((Bridge.stab ι J y : Subgroup Γ) : Set Γ).Finite := Set.finite_coe_iff.1 hf
  have ei : (fun γ => if γ ∈ Bridge.stab ι J y then F y else 0) =
      Set.indicator ((Bridge.stab ι J y : Subgroup Γ) : Set Γ) (fun _ => F y) := by
    funext γ; simp [Set.indicator]
  rw [ei, ← finsum_mem_def]
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset hs]
  rfl

theorem eq_sum_tr {I : Type} [Fintype I] {y : I → G} (hr : Bridge.IsReps ι J y)
    (hf : ∀ i, Finite (Bridge.stab ι J (y i))) {F : G → W} (hF : F ∈ GlobalTheory.ExportSeries.lawForms ι ρ J χ) :
    F = ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ • tr ι ρ J χ (y i) (F (y i)) := by
  funext x
  obtain ⟨i₀, ⟨γ₀, k₀, hx⟩, huniq⟩ := hr x
  rw [Finset.sum_apply, Finset.sum_eq_single i₀]
  · have hne : ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)) ≠ 0 := by
      haveI := hf i₀
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Pi.smul_apply, hx, tr_law (hf i₀), tr_self (hf i₀) hF, GlobalTheory.ExportSeries.mem_lawForms.1 hF γ₀ (y i₀) k₀, map_smul,
      smul_comm ((χ k₀ : ℂˣ) : ℂ) ((Nat.card (Bridge.stab ι J (y i₀)) : ℂ)), smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro i _ hi
    rw [Pi.smul_apply]
    have : tr ι ρ J χ (y i) (F (y i)) x = 0 := by
      unfold tr
      refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
      unfold term
      rw [dif_neg]
      intro h
      exact hi (huniq i ⟨γ, ⟨_, h⟩, by simp [mul_assoc]⟩)
    rw [this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LawTrace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LamVal

theorem exists_of_pow {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {a : FractionRing A} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ∃ y : A, algebraMap A (FractionRing A) y = a := by
  have hi : IsIntegral A a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  exact IsIntegrallyClosed.isIntegral_iff.1 hi

variable {D : D7}

theorem e_mem_of_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ρ.e i b a ∈ (ρ.eOk i b 0).range := by
  obtain ⟨y, rfl⟩ := exists_of_pow hn h
  exact ⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩

theorem de_mem {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eOk i b 0).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0)
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.ek_e, hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem typeCharacterExtension_mem_range_coefficientRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : G0 (Y.Z.ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (Y.Z.ρ.B i j b).G.P.H (⇑(Y.Z.ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  unfold ext1
  split_ifs with h
  · set g' := (Y.Z.ρ.eG i j b).symm g with hg'
    have hg : Y.Z.ρ.eG i j b g' = g := MulEquiv.apply_symm_apply _ _
    have h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H := by rw [hg]; exact h
    have hu : g' ∈ D.nexp.U := ((Y.Z.tie i j b).U_eq g').1 h'
    have e1 := (Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'
    have e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩ := by
      congr 1
      exact Subtype.ext hg.symm
    rw [e2, e1]
    have hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    apply (Y.Z.ρ.e i b).injective
    rw [map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]
  · exact one_mem _

theorem loc_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (PP : Pl D.host.E) (w : (kP PP)ˣ) :
    ((((Y.Z.ρ.B i j b).de.locC PP * (Y.Z.ρ.tw i b 0 ∅ 1).locC PP) w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1 := by
    simp [Twist.locC, Setup.tw, twistOf, half_empty]
  rw [hψ, mul_one]
  unfold Twist.locC
  split_ifs with hq
  · have hB := Y.Z.good.base i j b
    obtain ⟨P, -, hQ, hsp⟩ := hB.places.split
    obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w
    show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (hB.de.res PP hq)]
    exact de_mem Y.Z.good i j b x
  · simp

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem de_frac {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    ∃ d, ρ.e i b d = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) _
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem baseCharacter_finiteIdeles_mem_range_fractionRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ a, Y.Z.ρ.e i b a = (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) := by
  obtain ⟨y, hy⟩ := X.valKs j x hx
  refine ⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩
  rw [Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]
  refine Eq.trans ?_ hy.symm
  change D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _
  rw [Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]

theorem muC_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  obtain ⟨a, ha⟩ := baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf
  obtain ⟨d, hd⟩ := de_frac Y.Z.good i j b x
  have e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d) := by
    rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]
  haveI : Finite (kP PP)ˣ := inferInstance
  have hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [e2]
  refine e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_
  apply (Y.Z.ρ.e i b).injective
  rw [map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]

theorem levLam_mem_coef : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
    (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

end GlobalTheory.LamVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.baseLevelCharacter_mem_coefficientRing : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)), (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  first | exact @GlobalTheory.LamVal.levLam_mem_coef | exact GlobalTheory.LamVal.levLam_mem_coef | (intros; apply GlobalTheory.LamVal.levLam_mem_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFormsBaseLevelLeSpanIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000open Formalism.L2.Host (embLL0)

noncomputable section

namespace GlobalTheory.BaseSpan

variable {D : D7} {S T : HSp D}

theorem pq_le {B : Base S T} (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ T.rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

theorem coefLat_le_valSpace {B : Base S T} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} {y : Bridge.Gf S}
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) : P ∈ B.valSpace :=
  hspan ▸ Submodule.subset_span hP

theorem tr_mem_mtLat {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {ψ : Twist D Circle}
    (hlam : ∀ k, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ O) {y : Bridge.Gf S}
    (hf : Finite (Bridge.stab (Bridge.ratF S) (B.levJ ψ) y))
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) :
    GlobalTheory.LawTrace.tr (Bridge.ratF S) (B.act.comp (GQ S).subtype) (B.levJ ψ) (B.levLam ψ) y P ∈ B.mtLat σ emb O ψ := by
  refine (Base.mem_mtLat B σ emb O).2 ⟨Submodule.mem_inf.2 ⟨?_, GlobalTheory.LawTrace.mem_lawForms_tr hf P⟩, fun x => ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => GlobalTheory.LawTrace.tr_mem hf P x B.valSpace fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (coefLat_le_valSpace hspan hP))
  · refine GlobalTheory.LawTrace.tr_mem hf P x (B.coefLat σ emb O x) fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    have hx : x = Bridge.ratF S γ * y * ((⟨_, h⟩ : B.levJ ψ) : Bridge.Gf S) := by
      change x = Bridge.ratF S γ * y * ((Bridge.ratF S γ * y)⁻¹ * x)
      group
    have h1 := Base.act_mem_coefLat hB.frame hc γ y _ (Base.mem_St_of_mem_levJ (B := B) h) hP
    rw [← hx] at h1
    have h2 := Submodule.smul_mem (B.coefLat σ emb O x) (⟨_, hlam ⟨_, h⟩⟩ : O) h1
    exact h2

end GlobalTheory.BaseSpan

namespace GlobalTheory.BaseSpan

theorem tw_one_good {D : D7} {ρ : Setup D.ntw} (i : D.ntw.Tw) (b : Bool) :
    (ρ.tw i b 0 ∅ 1).Good ∧ (ρ.tw i b 0 ∅ 1).Q = ∅ := by
  have hc : (ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hq : (ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  refine ⟨⟨?_, fun x => ?_, fun a => ?_, ?_, fun x _ _ _ _ => ?_, fun PP h => ?_⟩, hq⟩
  · rw [hc, MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ
  · rw [hc]; rfl
  · rw [hc]; rfl
  · rw [hq]; exact splitSet_empty
  · rw [hc]; rfl
  · rw [hq] at h; exact absurd h (Finset.notMem_empty _)

theorem formsC_le_span_mt : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)) := by
  intro D X E Y i j b F hF
  have hρ : Y.Z.ρ.Good := Y.Z.good
  have hB : (Y.Z.ρ.B i j b).Good := hρ.base i j b
  obtain ⟨hψ, hψQ⟩ := tw_one_good (ρ := Y.Z.ρ) i b
  have hcls := hρ.classes i j b (Y.Z.ρ.tw i b 0 ∅ 1) hψ (by rw [hψQ]; exact Base.admissible_empty_of_good hB)
  have hlam : ∀ k, (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := fun k => GlobalTheory.T.baseLevelCharacter_mem_coefficientRing D X E Y i j b k
  have hL := (Submodule.mem_inf.1 hF).2
  rw [GlobalTheory.LawTrace.eq_sum_tr hcls.reps hcls.stab hL]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
  have hspan : Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D) (Y.Z.ρ.eOk i b 0).range
      (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) = (Y.Z.ρ.B i j b).valSpace :=
    (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS _
      (embLL0 D) (labLL0 D) _ _ hB.wt (pq_le hB) (hρ.isCoefRing_k i b 0)
      (GlobalTheory.LatFull.latAt_isFullLattice D Y.Z.ρ hρ i j b _)).2
  have hFy : F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) ∈ Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D)
      (Y.Z.ρ.eOk i b 0).range (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    rw [hspan]
    exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hF).1) _ trivial
  generalize F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) = v at hFy ⊢
  induction hFy using Submodule.span_induction with
  | mem P hP =>
    exact Submodule.subset_span (tr_mem_mtLat hB (hρ.isCoefRing_k i b 0) hlam (hcls.stab c) hspan hP)
  | zero =>
    rw [GlobalTheory.LawTrace.tr_zero]
    exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [GlobalTheory.LawTrace.tr_add (hcls.stab c)]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [GlobalTheory.LawTrace.tr_smul]
    exact Submodule.smul_mem _ _ hP

end GlobalTheory.BaseSpan

end
end
end
