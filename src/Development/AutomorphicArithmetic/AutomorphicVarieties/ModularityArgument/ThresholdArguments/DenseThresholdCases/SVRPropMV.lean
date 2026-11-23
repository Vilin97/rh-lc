module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExLLeOfCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CmpResplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.Esk.PropMVAux

variable {l : ℕ} [Fact l.Prime]

theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : Qbar l)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at h2

def oneU (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : ((a * b : (Qbar l)ˣ) : Qbar l) - 1 = a * (b - 1) + (a - 1) := by rw [Units.val_mul]; ring
    show ‖_‖ < 1
    rw [e]
    refine add_lt ?_ ha
    rw [norm_mul, norm_one_of ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    have e : (a : Qbar l) * (((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(a - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_one_of ha, one_mul, norm_neg] at h
    show ‖_‖ < 1
    rw [h]
    exact ha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem cyc_mem (s : G F Ω) : cycBar F Ω l s ^ (l - 1) ∈ oneU l := by
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - 1 =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l])) ^ _ - 1 = _
    simp
  show ‖_‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

theorem cont_cyc : Continuous (cycBar F Ω l) :=
  have h : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom h).comp (continuous_cycZ F Ω l)

theorem cyc_frob [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : Pl F} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  change algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l σ : ℤ_[l]) : ℚ_[l]) = _
  rw [cycZ_of_isFrob hl h hσ]
  simp

theorem fin_l : {w : Pl F | ((l : ℕ) : 𝓞 F) ∈ w.asIdeal}.Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

theorem cond_ex (ω : HChar F) {m : ℕ} (hm : 0 < m) (h : ω.OrderDvd m) :
    ∃ c : Pl F → ℕ, (∀ w, IsCondAt w ω (c w)) ∧ (∀ w, c w = 0 ↔ ω.UnrAt w) ∧ {w | c w ≠ 0}.Finite := by
  classical
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  have hex : ∀ w, ∃ n, ω.LevelLe w n := fun w => ⟨M, fun x hu hx => key w x hu fun _ => hx⟩
  have h0 : ∀ w, Nat.find (hex w) = 0 ↔ ω.UnrAt w := fun w => by rw [Nat.find_eq_zero, HChar.unrAt_iff]
  refine ⟨fun w => Nat.find (hex w), fun w => ⟨Nat.find_spec (hex w), fun n hn => Nat.find_min' (hex w) hn⟩, h0,
    hS.subset fun w hw => ?_⟩
  by_contra hS
  exact hw ((h0 w).2 fun x hx => key w x hx fun h => absurd h hS)

theorem loc_zpow {ω : HChar F} {w : Pl F} (hu : ω.UnrAt w) (x : (w.adicCompletion F)ˣ) :
    ∃ n : ℤ, ω.loc w x = ω.val w ^ n := by
  have hx0 : Valued.v (x : w.adicCompletion F) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x : w.adicCompletion F) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hun : IsUnitAt w (x * atFin w (unif w) ^ n) := by
    have h2 := unif_spec w
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, hn, ← WithZero.exp_add]
    simp
  have h3 := hu _ hun
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact ⟨_, h3⟩

theorem closed_oneU : IsClosed (oneU l : Set (Qbar l)ˣ) := by
  have : IsClosed {x : Qbar l | ‖x - 1‖ < 1} := by
    simpa only [Metric.ball, dist_eq_norm] using IsUltrametricDist.isClosed_ball (1 : Qbar l) 1
  exact this.preimage Units.continuous_val

theorem dec_cong {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {ω : HChar F}
    {ξ : G F Ω →* (Qbar l)ˣ} (hc : Continuous ξ) (hL : IsLAdicOf art ι ω 0 ξ) {w : Pl F} (hu : ω.UnrAt w)
    (hv : ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) : Cong (ξ σ) 1 := by
  have hm : toAb F Ω σ ∈ (art.comp (localIdele F w)).range.topologicalClosure := by
    rw [ha.dec w A hA]
    exact ⟨σ, hσ, rfl⟩
  have hle : (art.comp (localIdele F w)).range ≤ (oneU l).comap (liftAb ξ hc) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele F w x))
    obtain ⟨n, hn⟩ := loc_zpow hu x
    have hv' : Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ∈ oneU l := hv
    have e : ξ τ = Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ^ n := by
      rw [← map_zpow, ← hn]
      exact Units.ext (hL.loc_away (Or.inr rfl) x τ hτ.symm)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← hτ, liftAb_toAb, e]
    exact zpow_mem hv' _
  have h := Subgroup.topologicalClosure_minimal _ hle (closed_oneU.preimage (continuous_liftAb ξ hc)) hm
  rw [Subgroup.mem_comap, liftAb_toAb] at h
  exact h

theorem tr_det (ι : Qbar l ≃+* ℂ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (a b : ℂ)
    (h : M.charpoly.map ι.toRingHom = Polynomial.X ^ 2 - C a * Polynomial.X + C b) : M.trace = ι.symm a ∧ M.det = ι.symm b := by
  rw [Matrix.charpoly_fin_two] at h
  have h2 := congrArg (AddMonoidAlgebra.coeff · 1) h
  have h3 := congrArg (AddMonoidAlgebra.coeff · 0) h
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C] at h2 h3
  rw [← h2, ← h3]
  simp

theorem det_res [IsAlgClosure F Ω] (ξ : G F Ω →* (Qbar l)ˣ) (hξ : Continuous ξ) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (hr : Continuous r) (k : ℕ) (hk : l - 1 ∣ k) (hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ‖(r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ σ⁻¹)‖ < 1 ∧
      (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ σ⁻¹ * (cycBar F Ω l σ : Qbar l) ^ k) :
    Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ (-(k : ℤ)) * ξ ∧ ResSum r ![1, ξ] := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hr.comp continuous_inv)
  have c2 : Continuous fun g : G F Ω => (ξ g⁻¹ : Qbar l) := Units.continuous_val.comp (hξ.comp continuous_inv)
  have c3 : Continuous fun g : G F Ω => (cycBar F Ω l g : Qbar l) := Units.continuous_val.comp cont_cyc
  have hdet : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ g⁻¹ * (cycBar F Ω l g : Qbar l) ^ k := fun g => by
    refine congrFun (Continuous.ext_on hD c1.matrix_det (c2.mul (c3.pow k)) ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).2
  have htr : ∀ g : G F Ω, ‖(r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g⁻¹)‖ < 1 := fun g => by
    have h0 : IsClosed {x : Qbar l | ‖x‖ < 1} := by
      simpa only [Metric.ball, dist_zero_right] using IsUltrametricDist.isClosed_ball (0 : Qbar l) 1
    have h1 := h0.preimage (c1.matrix_trace.sub (continuous_const.add c2 : Continuous fun g : G F Ω => 1 + (ξ g⁻¹ : Qbar l)))
    refine h1.closure_subset_iff.2 ?_ (hD g)
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).1
  refine ⟨MonoidHom.ext fun g => Units.ext ?_, fun g i => ?_⟩
  · have h1 := hdet g⁻¹
    rw [inv_inv] at h1
    change (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((cycBar F Ω l g ^ (-(k : ℤ)) * ξ g : (Qbar l)ˣ) : Qbar l)
    rw [h1]
    simp [mul_comm]
  · have h1 := hdet g⁻¹
    have h2 := htr g⁻¹
    rw [inv_inv] at h1 h2
    have h3 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g‖ < 1 := by
      obtain ⟨t, rfl⟩ := hk
      have h4 : ‖((cycBar F Ω l g⁻¹ ^ ((l - 1) * t) : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := by
        rw [pow_mul]; exact pow_mem (cyc_mem g⁻¹) t
      rw [h1, ← mul_sub_one, norm_mul, hn, one_mul, ← Units.val_pow_eq_pow_val]
      exact h4
    have e : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (Polynomial.X - C ((![1, ξ] j g : (Qbar l)ˣ) : Qbar l)) =
        C (-((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g))) * Polynomial.X + C ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g) := by
      rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_neg, map_sub, map_add (f := _), map_one]
      ring
    rw [← coeff_sub, e]
    rcases i with _ | _ | i
    · rwa [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
    · rwa [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, norm_neg]
    · rw [coeff_add, coeff_mul_X, coeff_C_succ, coeff_C_succ, add_zero, norm_zero]
      exact zero_lt_one

theorem norm_eq_one {x y : Qbar l} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - y‖ ≠ ‖y‖ := by rw [hy]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, hy, max_eq_right h.le] at h2

theorem nu_lt {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x < 1 ↔ ‖ι.symm x‖ < 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_lt_one, coe_nnnorm]

theorem nu_eq {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x = 1 ↔ ‖ι.symm x‖ = 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_eq_one, coe_nnnorm]

open Classical in
theorem prod_away {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = 1 :=
  Finset.prod_eq_one fun v _ => by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (h ▸ D.mem v)

open Classical in
theorem prod_at {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F) (v₀ : InfinitePlace F)
    (hv : D.pl v₀ = w) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = if v₀ ∈ S then (l : ℂ) ^ t else 1 := by
  rw [Finset.prod_eq_single v₀ (fun v _ hne => if_neg fun h => hne (D.inj (h.1.trans hv.symm)))
    (fun h => absurd (Finset.mem_univ _) h)]
  by_cases h : v₀ ∈ S <;> simp [hv, h]

end UpperTheory.Esk.PropMVAux
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRPropMV

section

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add (f := _)]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add (f := _), map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
end
end
end
