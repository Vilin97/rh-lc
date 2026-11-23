module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.HeckeMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.JacNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.KerKill
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
public import Mathlib.LinearAlgebra.PID
public import Mathlib.RingTheory.Finiteness.Nilpotent
import Mathlib.Tactic.Linter.Style
import GroundTheory.AutomorphicForms.MeasuresGL

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosOp

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuotAlt

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dite_eq_left hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), hzero, add_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CasTrace

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}

private def pw (σ : k ≃+* k) (t : Fin n → kˣ) : ℕ → Fin n → kˣ
  | 0 => 1
  | m + 1 => t * fun i => Units.map (σ : k →* k) (pw σ t m i)

private theorem val_pw {σ : k ≃+* k} (h : Isom σ) (t : Fin n → kˣ) (i : Fin n) :
    ∀ m, valuation k (pw σ t m i : k) = valuation k (t i : k) ^ m
  | 0 => by simp [pw]
  | m + 1 => by
    have := h (pw σ t m i)
    simp only [pw, Pi.mul_apply, Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe, this, val_pw h t i m, pow_succ']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_diag (σ : k ≃+* k) (s : Fin n → kˣ) :
    Loc.sg σ (diagT k (Fin n) s) = diagT k (Fin n) fun i => Units.map (σ : k →* k) (s i) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sg_val, val_diagT, val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem small {t : Fin n → kˣ} (ht : Strict t) {r : ValueGroupWithZero k} (hr : r ≠ 0) :
    ∀ᶠ m : ℕ in atTop, ∀ i j, i < j → valuation k (t i : k) ^ m ≤ r * valuation k (t j : k) ^ m := by
  simp only [eventually_all]
  intro i j hij
  have h0 : valuation k (t j : k) ≠ 0 := by simp
  have h1 : valuation k (t i : k) / valuation k (t j : k) < 1 := (div_lt_one₀ (zero_lt_iff.2 h0)).2 (ht i j hij)
  obtain ⟨M, hM⟩ := exists_pow_lt₀ h1 (Units.mk0 r hr)
  filter_upwards [eventually_ge_atTop M] with m hm
  have h2 : (valuation k (t i : k) / valuation k (t j : k)) ^ m ≤ r := (pow_le_pow_right_of_le_one' h1.le hm).trans hM.le
  rwa [div_pow, div_le_iff₀ (zero_lt_iff.2 (pow_ne_zero _ h0))] at h2

private theorem unif {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {e : V →ₗ[ℂ] V} (he : IsAvg π K e) (Z : Submodule ℂ V)
    [FiniteDimensional ℂ Z] (hZ : Z ≤ twKer π (unipB k (Fin n)) 1) {t : Fin n → kˣ} (ht : Strict t) {σ : k ≃+* k} (h : Isom σ) :
    ∃ m, 0 < m ∧ ∀ v ∈ Z, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
  obtain ⟨s, hs⟩ := (Submodule.fg_top Z).1 (Module.finite_def.1 inferInstance)
  have : ∀ᶠ m : ℕ in atTop, ∀ v ∈ s, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
    rw [eventually_all_finset]
    intro v hv
    obtain ⟨r, hr, hk⟩ := kerKill k n V π K hK e he v (hZ (hs ▸ Submodule.subset_span hv))
    filter_upwards [small ht hr] with m hm
    exact hk _ fun i j hij => by rw [val_pw h, val_pw h]; exact hm i j hij
  obtain ⟨m, hm, h0⟩ := (this.and (eventually_gt_atTop 0)).exists
  refine ⟨m, h0, fun v hv => ?_⟩
  have : Z ≤ LinearMap.ker (e ∘ₗ π (diagT k (Fin n) (pw σ t m))) := hs ▸ Submodule.span_le.2 hm
  exact this hv

end SlopeTestRemainingChoices

private theorem trIn_smul' {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (c • T) = c * trIn P T := by
  have h' : ∀ y ∈ P, (c • T) y ∈ P := fun y hy => P.smul_mem c (h y hy)
  rw [trIn, trIn, dite_eq_left h, dite_eq_left h', ← smul_eq_mul, ← map_smul]
  rfl

theorem UpperTheory.Gal.Join.casTrace :
    UpperTheory.Gal.Join.CasTrace := by
  intro k _ _ _ _ n V _ _ π ha _ _ μ _ K hK σ A hA hσ hst t ht
  have hd : Dom t := fun i j h => (ht i j h).le
  obtain ⟨e, he, hc⟩ := avgEx _ V π ha.1 K hK.co
  have hAe : ∀ v, A (e v) = e (A v) := hc (Loc.sg σ) A hA (fun g hg => (hst g).2 hg) fun g hg => by
    have e1 : Loc.sg σ (Loc.sg σ.symm g) = g := Units.ext (Matrix.ext fun i j => σ.apply_symm_apply _)
    exact ⟨Loc.sg σ.symm g, (hst _).1 (by rwa [e1]), e1⟩
  have hfix : ∀ v ∈ fixed π K, A v ∈ fixed π K := fun v hv => by rw [← he.fix v hv, hAe]; exact he.mem _
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k n μ
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hK.co.2 hK.co.1
  refine ⟨_, dcosOp _ V μ π ha.1 K hK.co e he (diagT k (Fin n) t), ?_⟩
  obtain ⟨-, s1, s2⟩ := imStab k n V π ha K hK
  change HasFinTrace (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) _
  have hq : ((Real.sqrt (deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have key := traceQuot V _ (fixed π K) (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A)
    (twKer π (unipB k (Fin n)) 1).mkQ
    (((μ.real (K : Set (GL (Fin n) k)) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹) • (jacB π t ∘ₗ jacA hA))
    (fun v => Submodule.smul_mem _ _ (he.mem _)) (fun v hv => ?_) fun v hv h0 => ?_
  · rwa [trIn_smul' (P := (fixed π K).map (twKer π (unipB k (Fin n)) 1).mkQ) (T := jacB π t ∘ₗ jacA hA)
      fun y hy => s1 t _ (s2 σ A hA hst y hy)] at key
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [he.fix _ (hfix v hv), (heckeMul k n V π K hK e he t hd _ (hfix v hv)).2, jacNorm k n V π, smul_smul,
      (dcosVol k n μ K hK t hd).2]
    congr 1
    have h2 : ((deltaB t : ℝ) : ℂ) = ((Real.sqrt (deltaB t) : ℝ) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt (deltaB_pos t).le).symm
    push_cast
    rw [h2]
    field_simp
  · obtain ⟨m, -, hm⟩ := unif hK he (fixed π K ⊓ twKer π (unipB k (Fin n)) 1) inf_le_right ht hσ
    have hZ : ∀ j : ℕ, (A ^ j) v ∈ fixed π K ⊓ twKer π (unipB k (Fin n)) 1 := fun j => by
      induction j with
      | zero => exact ⟨hv, (Submodule.Quotient.mk_eq_zero _).1 h0⟩
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨hfix _ ih.1, (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
        rw [← jacA_mk hA, (Submodule.Quotient.mk_eq_zero _).2 ih.2, map_zero]
    have hP : ∀ j : ℕ, ((((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) ^ j) v =
        (μ.real (dcos K t) : ℂ) ^ j • e (π (diagT k (Fin n) (pw σ t j)) ((A ^ j) v)) := fun j => by
      induction j with
      | zero => simp [pw, he.fix v hv]
      | succ j ih =>
        have hdj : Dom fun i => Units.map (σ : k →* k) (pw σ t j i) := fun a b hab => by
          have h1 := hσ (pw σ t j a)
          have h2 := hσ (pw σ t j b)
          simp only [Units.coe_map, MonoidHom.coe_coe, h1, h2, val_pw hσ]
          exact pow_le_pow_left' (hd a b hab) j
        rw [pow_succ', Module.End.mul_apply, ih, map_smul]
        simp only [LinearMap.comp_apply, LinearMap.smul_apply]
        rw [hAe, he.fix _ (he.mem _), hA, sg_diag, (heckeMul k n V π K hK e he _ hdj _ (hfix _ (hZ j).1)).1 t hd, smul_smul,
          ← pow_succ, pow_succ' A]
        rfl
    exact ⟨m, by rw [hP, hm _ (hZ m), smul_zero]⟩
end
end
