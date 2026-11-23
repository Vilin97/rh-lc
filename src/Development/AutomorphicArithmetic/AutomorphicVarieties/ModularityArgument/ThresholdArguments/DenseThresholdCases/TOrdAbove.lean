module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CentralCharSqEqOfIsSelfDualBy
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfDualR
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterContinuous
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeCharLocalArtinEqCyclotomicTwist

section

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (ξ : G F Ω →* (Qbar l)ˣ) (t : ℤ), IsOpen (ξ.ker : Set (G F Ω)) → IsCharOf ι χ (cycBar F Ω l ^ t * ξ) → ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, ((χ.loc w (a s) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (t * deg s) * ι (ξ (s : G F Ω) : Qbar l) := by
  intro N F Ω _ _ _ _ _ l _ ι χ ξ t hξ ⟨hc, art, n, hart, _, hL⟩ w hw A h a ha s
  haveI : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen hξ
  have hN : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := UpperTheory.V.Loc.laHecke h art hart ι χ n _ hL ⟨a, ha⟩
  have h2 := UpperTheory.V.Loc.laArith N.aut.art h hw ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype)
    (hc.comp continuous_subtype_val) t ξ.ker.index (Nat.pos_of_ne_zero hN) fun g _ => by
      have e : ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype) g * cycBar F Ω l g ^ (-t) = ξ g := by
        show cycBar F Ω l g ^ t * ξ g * cycBar F Ω l g ^ (-t) = ξ g
        rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, ← map_pow]
      exact ξ.ker.pow_index_mem _
  have h3 := UpperTheory.V.Loc.laUnique h ⟨a, ha⟩ _ _ _ h1 h2
  haveI : Fintype {j : w.adicCompletion F →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb w)
  have h4 : locPow ι n w (a s : w.adicCompletion F) = Hi.algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ t := by
    unfold locPow Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_injective (congrFun h3 j), zpow_one]
  have h0 : Hi.algPow w (fun _ : F →+* Qbar l => 1) (a s : w.adicCompletion F) ^ t ≠ 0 := by
    refine zpow_ne_zero _ ?_
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero)
  have h5 := hL.loc (a s) s (ha.glob art hart s)
  have h6 := UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s
  have h7 : (((cycBar F Ω l ^ t * ξ) (s : G F Ω) : (Qbar l)ˣ) : Qbar l) =
      (cycBar F Ω l (s : G F Ω) : Qbar l) ^ t * (ξ (s : G F Ω) : Qbar l) := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul]
    rfl
  rw [h7, h6, h4, mul_zpow, mul_right_comm, mul_left_inj' h0, eq_comm, RingEquiv.symm_apply_eq] at h5
  rw [h5, map_mul, map_zpow₀, map_zpow₀, map_natCast, ← zpow_mul, mul_comm t]
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdAbove

section

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Sd.OrdinaryAbove
section Loc
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
private theorem norm_fin {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (ξ : G F Ω →* (Qbar l)ˣ) (hξ : IsOpen (ξ.ker : Set (G F Ω))) (g : G F Ω) : ‖(ξ g : Qbar l)‖ = 1 := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ (g ^ ξ.ker.index) = 1 := Subgroup.pow_index_mem ξ.ker g
  have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2
private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem cont_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc F Ω l
theorem central_weil_ordinary_above (hP : _root_.UpperTheory.V.Af.HypothesesH') {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r}
    (H : OrdForm ι ξ s c m a π r) {w : HeightOneSpectrum (𝓞 F)} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {ar : Weil h →* (w.adicCompletion F)ˣ} (har : IsLocalArtin h ar)
    {σ : SmIrr (GL (Fin 2) (w.adicCompletion F))} (hσ : LocIsotypic π.finPart w σ) (t : Weil h) (z : ℂ)
    (hz : ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ar t)) v = z • v) :
    ‖ι.symm z‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ ((s + 1) * deg t) := by
  have e : Matrix.GeneralLinearGroup.det.comp r * cycBar F Ω l ^ (((2 : ℕ) : ℤ) - 1) = cycBar F Ω l ^ (s + 1) * ξ := by
    rw [H.det, _root_.zpow_add, mul_right_comm]
    norm_num
  have hc : Continuous (cycBar F Ω l ^ (s + 1) * ξ : G F Ω →* (Qbar l)ˣ) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.continuous_det.comp H.cont).mul ((cont_cyc F Ω l).zpow _)
  obtain ⟨χ, hχ⟩ := (_root_.UpperTheory.V.Af.algOfCyc_s hP F Ω l ι).1 _ hc fun v hv => by
    have hA := isPlaceOver_placeOf Ω v
    refine ⟨_, hA, s + 1, 1, one_pos, fun g hg => ?_⟩
    have h1 : ξ g = 1 := (H.ram v _ hA).2 (Or.inr hv) hg
    rw [pow_one, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  have hd := (_root_.UpperTheory.V.Af.self_dual_real_of_printed_hida hP F Ω l ι 2 one_le_two r π H.att _ χ (dualTw_det r) (e ▸ hχ)).1
  have h1 := UpperTheory.central_char_sq_eq_of_isSelfDualBy F π χ hd w σ hσ _ z hz
  rw [_root_.UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' hP.litN F Ω l ι χ ξ (s + 1) H.ξ_open hχ w hw A h ar har t] at h1
  have h2 := congrArg (fun x => ‖ι.symm x‖) h1
  simp only [map_pow, map_mul, map_zpow₀, map_natCast, RingEquiv.symm_apply_apply, norm_pow, norm_mul, norm_zpow,
    norm_fin ξ H.ξ_open, mul_one] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) two_ne_zero).1 h2
end UpperTheory.V.Sd.OrdinaryAbove
end
end
end
