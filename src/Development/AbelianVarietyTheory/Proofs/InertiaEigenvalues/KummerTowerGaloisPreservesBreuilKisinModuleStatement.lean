module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismGaloisLiftIsPrismHom

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PrismTwist

variable {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e)

theorem ev_injective : Function.Injective (ϖ.ev a) := by
  apply GlobalTheory.BKCoord.ev_injective <;> assumption

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff, WittVector.map_coeff, GlobalTheory.RingIface.sigA_coeff,
    frobenius_def, frobenius_def, map_pow]

end GlobalTheory.BKGal.PrismTwist

theorem GlobalTheory.BKGal.PrismTwist.hom_restrict : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  intro l _ a e _ _ ϖ g σ hσ ψ hψ
  have hfrob : ∀ x, ψ (frobS l a x) = frobS l a (ψ x) := fun x =>
    GlobalTheory.BKGal.PrismTwist.ev_injective a ϖ (by
      rw [hψ, PiSys.ev_frobS, PiSys.ev_frobS, hψ, GlobalTheory.BKGal.PrismTwist.σA_frobenius])
  refine ⟨{ f := ψ
            f_δ := (deltaS l a).map_δ_of_map_φ (deltaS l a)
              (fun x hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) ψ hfrob
            f_I := fun (x : (Wq l a)⟦X⟧) hx => ?_
            f_str := fun r (x : (Wq l a)⟦X⟧) h => ?_ }, fun _ => rfl⟩
  · have hx' := Ideal.mem_span_singleton.1 hx
    refine Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a (ψ x)).1 ?_)
    rw [hψ, GlobalTheory.RingBasics.θ_σA, (ϖ.theta_ev_eq_zero_iff a x).2 hx', map_zero]
  · apply ϖ.quotToOC_injective a
    change ϖ.quotToOC a (Ideal.Quotient.mk _ (ψ x)) = ϖ.quotToOC a (ϖ.strMap a (σ r))
    have h' : Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r := h
    rw [PiSys.quotToOC_mk, PiSys.quotToOC_strMap, hψ, GlobalTheory.RingBasics.θ_σA, ← PiSys.quotToOC_mk, h',
      PiSys.quotToOC_strMap]
    refine Subtype.ext ?_
    rw [GlobalTheory.RingIface.sigO_coe]
    change Per.σC g (((r : ↥(ϖ.field a).1) : Om l) : ℂ_[l]) = (((σ r : ↥(ϖ.field a).1) : Om l) : ℂ_[l])
    rw [hσ]
    exact GlobalTheory.RingBasics.σC_coe g _
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismGaloisLiftIsPrismHomStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  first | exact @GlobalTheory.BKGal.PrismTwist.hom_restrict | exact GlobalTheory.BKGal.PrismTwist.hom_restrict | (intros; apply GlobalTheory.BKGal.PrismTwist.hom_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversTameActsRingEndoWittPowerSeries

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverRing

variable {l : ℕ} [hl : Fact l.Prime]

theorem smul_eq_zero_ainf {c : ℤ_[l]} (hc : c ≠ 0) {z : Ainf l} (h : c • z = 0) : z = 0 := by
  have h1 := PadicInt.unitCoeff_spec hc
  rw [h1, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc] at h
  have h2 : (l : Ainf l) ^ c.valuation * z = 0 :=
    ((PadicInt.unitCoeff hc).isUnit.map (algebraMap ℤ_[l] (Ainf l))).mul_right_eq_zero.1 h
  have key : ∀ n : ℕ, ∀ z : Ainf l, (l : Ainf l) ^ n * z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih => intro z h; exact ih z (ainf_torsionFree _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact key _ z h2

theorem one_tmul_inj {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Nontrivial O]
    {x y : Ainf l} (h : (1 : O) ⊗ₜ[ℤ_[l]] x = (1 : O) ⊗ₜ[ℤ_[l]] y) : x = y := by
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_zero (b.repr.injective (by ext i; simp [hc i]))
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] (Ainf l) ((b.coord i).rTensor (Ainf l) w)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (smul_eq_zero_ainf hi h1)

variable {a : ℕ} [NeZero a]

theorem exists_root {e : ℕ} [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]
    (γ : TameGal ↥LL.1 l e a) :
    ∃ c : Wq l a, ∀ τ, algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ c) = γ.root τ := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have he : e = l ^ a - 1 := by
    have := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a); omega
  set w : ↥LL.1 := ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) with hwdef
  have hw : (w : Om l) = ω := by
    refine (algebraMap (Om l) ℂ_[l]).injective ?_
    have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
    simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
    exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)
  have hwp : IsPrimitiveRoot w e := by
    rw [he]
    refine IsPrimitiveRoot.of_map_of_injective (f := (LL.1).val) ?_ Subtype.val_injective
    simpa [hw] using hω
  have hpow : (((γ.left : (↥LL.1)ˣ) : ↥LL.1)) ^ e = 1 := (mem_rootsOfUnity' _ _).1 γ.left.2
  obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one hpow
  refine ⟨WittVector.teichmuller l z ^ k, fun τ => ?_⟩
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z ^ k)) : ↥(OL LL)) : ↥LL.1) = _
  rw [map_pow, sigma_pow_teich, map_pow, map_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hwdef,
    TameGal.root, powL_apply]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hk]
  ring

end GlobalTheory.BKGal.CoverRing


open GlobalTheory.BKGal.CoverRing GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_ringEndo : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a),
    Covers ↥LL.1 (thetaW a LL) ϖ g γ →
      ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  intro l _ a e _ _ ϖ LL _ _ g γ hcov
  obtain ⟨c, hc⟩ := exists_root LL γ
  refine ⟨(rescale c).comp (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
    Wq l a →+* Wq l a)), fun x => ?_⟩
  have h := hcov (toAc (thetaW a LL) ↥LL.1 x)
    (toAc (thetaW a LL) ↥LL.1 (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x))) (fun τ => toAc_rescale (thetaW a LL) γ c hc x τ)
  rw [PiSys.iTot_toAc, PiSys.iTot_toAc, galOA_tmul] at h
  exact (one_tmul_inj h).symm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversTameActsRingEndoWittPowerSeriesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ g γ → ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  first | exact @GlobalTheory.BKGal.covers_ringEndo | exact GlobalTheory.BKGal.covers_ringEndo | (intros; apply GlobalTheory.BKGal.covers_ringEndo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGaloisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.realisesEtaleFCrystal_pullback_galois : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (E : FCrys l ↥(OL K)) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∀ (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K)), (∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) → (∀ h ∈ GK K, g⁻¹ * h * g ∈ GK K) → ∀ (ρg : T ≃ₗ[ℤ_[l]] T), (∀ h h' : ↥(GK K), (h' : GQ l) = g⁻¹ * h * g → ∀ x, ρg (ρ h' x) = ρ h (ρg x)) → ∃ (gH : Hom (ainfObj K) ((ainfObj K).restrict σ)) (j' : (E.pullback σ).M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), (∀ x, gH.f x = Per.σA g x) ∧ Realises K (E.pullback σ) (ainfObj K) (ainfId K) T ρ j' ∧ ∀ z, j' (E.tr gH z) = TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j z) := by
  first | exact @GlobalTheory.Prism.PullGal.realises_pullback | exact GlobalTheory.Prism.PullGal.realises_pullback | (intros; apply GlobalTheory.Prism.PullGal.realises_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModule

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GKinfStable
variable {l : ℕ} [hl : Fact l.Prime]

theorem map_field_le (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l)
    {x : Om l} (hx : x ∈ (ϖ.field a).1) : g x ∈ (ϖ.field a).1 := by
  have hd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have := ϖ.isGalois_field a hd
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩

theorem conj_mem (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∀ h ∈ GK (ϖ.field a), g⁻¹ * h * g ∈ GK (ϖ.field a) := by
  intro h hh
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh (g x) (map_field_le a e ϖ he g hx)
  simp only [AlgEquiv.mul_apply, h1]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem res_exists (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∃ σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a)),
      ∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l) := by
  let F := (ϖ.field a).1
  let φ : ↥F →ₐ[ℚ_[l]] ↥F :=
    { toFun := fun y => ⟨g y, map_field_le a e ϖ he g y.2⟩
      map_one' := Subtype.ext (map_one g : g (1 : Om l) = 1)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : Om l) (z : Om l))
      map_zero' := Subtype.ext (map_zero g : g (0 : Om l) = 0)
      map_add' := fun y z => Subtype.ext (map_add g (y : Om l) (z : Om l))
      commutes' := fun q => Subtype.ext (g.commutes q) }
  refine ⟨{ toFun := fun x => ⟨φ x, x.2.map (φ.restrictScalars ℤ_[l])⟩
            map_one' := Subtype.ext (map_one φ : φ (1 : ↥F) = 1)
            map_mul' := fun y z => Subtype.ext (map_mul φ (y : ↥F) (z : ↥F))
            map_zero' := Subtype.ext (map_zero φ : φ (0 : ↥F) = 0)
            map_add' := fun y z => Subtype.ext (map_add φ (y : ↥F) (z : ↥F)) }, fun x => rfl⟩

theorem kappa_act {LL : FinExt l} (T : QLat LL) (g : Gl l) (z : letI := zlLat T; WCb l ⊗[ℤ_[l]] ↥T.L.T) :
    letI := zlLat T
    TWact (galOW (↥(OL LL)) (sQ l g)) T g (kappa T z) =
      kappa T (TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) z) := by
  letI := zlLat T
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actZ_mul_apply {LL : FinExt l} (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T g (actZ T h x) = actZ T (g * h) x :=
  Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g h) (x : T.V)).symm

theorem actZ_one_apply {LL : FinExt l} (T : QLat LL) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T 1 x = x :=
  Subtype.ext (LinearMap.congr_fun (map_one T.ρ) (x : T.V))

end GlobalTheory.GKinfStable


open GlobalTheory.GKinfStable in
theorem GlobalTheory.GKinfStable.main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  intro BS l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK g γ hcov v hv
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1)
  choose σ hσ using res_exists (l := l) a e ϖ he (sQ l g)
  choose ψ hψ using GlobalTheory.T.covers_tame_acts_ringEndo_wittPowerSeries a e ϖ LL (sQ l g) γ hcov
  choose H hH using GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom a e ϖ (sQ l g) σ hσ ψ hψ
  letI := zlLat T
  obtain ⟨E, j, hR, hiff⟩ := hBK
  let ρg : ↥T.L.T ≃ₗ[ℤ_[l]] ↥T.L.T :=
    LinearEquiv.ofLinear (actZ T g) (actZ T g⁻¹)
      (LinearMap.ext fun x => (actZ_mul_apply T g g⁻¹ x).trans
        ((congrArg (fun k => actZ T k x) (mul_inv_cancel g)).trans (actZ_one_apply T x)))
      (LinearMap.ext fun x => (actZ_mul_apply T g⁻¹ g x).trans
        ((congrArg (fun k => actZ T k x) (inv_mul_cancel g)).trans (actZ_one_apply T x)))
  have hPR := GlobalTheory.T.realisesEtaleFCrystal_pullback_galois (ϖ.field a) E ↥T.L.T _ j hR (sQ l g) σ hσ
    (conj_mem (l := l) a e ϖ he (sQ l g)) ρg (fun h h' hh x => by
      have e2 : g * inclG (ϖ.field a) h' = inclG (ϖ.field a) h * g := by
        rw [show inclG (ϖ.field a) h' = g⁻¹ * inclG (ϖ.field a) h * g from Subtype.ext hh]
        group
      exact (actZ_mul_apply T g _ x).trans ((congrArg (fun k => actZ T k x) e2).trans
        (actZ_mul_apply T _ g x).symm))
  choose gH j' hgH hR' hj' using hPR
  have hBS := (BS l (ϖ.field a) (ainfObj _) (ainfId _) (isAinf_ainfObj _)).2 ↥T.L.T ↥T.L.T _ _
    (E.pullback σ) E j' j hR' hR LinearMap.id (fun _ _ => rfl)
  choose u hu using hBS.exists
  have hx := (hiff (I.j (toW (thetaW a LL) ϖ P v))).2 ⟨v.1, hv, rfl⟩
  choose x hx using hx
  have hm := (hiff (kappa T (j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x)))))).1 ⟨_, rfl⟩
  choose m' hm' hm'eq using hm
  have e1 : gH.comp (ϖ.toAinf a) = ((ϖ.toAinf a).restrict σ).comp H :=
    Hom.ext' (RingHom.ext fun y => by
      change gH.f (ϖ.ev a y) = ϖ.ev a (H.f y)
      rw [hH]
      exact (hgH _).trans (hψ y).symm)
  have key : TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) (j (E.tr (ϖ.toAinf a) x)) =
      j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x))) := by
    have h2 : j (u.u (ainfObj _) ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x))) =
        j' ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x)) := by
      refine (hu _).trans ?_
      exact LinearMap.lTensor_id_apply _ _ _
    refine (hj' (E.tr (ϖ.toAinf a) x)).symm.trans ?_
    refine Eq.trans ?_ ((congrArg j (u.u_tr (ϖ.toAinf a) (E.tr H x))).symm.trans h2).symm
    refine congrArg j' ?_
    refine ((E.tr_comp _ _ x).symm).trans ?_
    refine (congrArg (fun f => E.tr f x) e1).trans ?_
    exact E.tr_comp _ _ x
  refine ⟨⟨m', mem_ME_of_mem_M hm'⟩, hm', ?_⟩
  apply I.j.injective
  refine (Ident.j_act _ _ _ _).trans ?_
  refine Eq.trans ?_ hm'eq
  refine (congrArg (TWact (galOW (↥(OL LL)) (sQ l g)) T g) hx).trans ?_
  exact (kappa_act T g _).trans (congrArg _ key)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModuleStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  first | exact @GlobalTheory.GKinfStable.main | exact GlobalTheory.GKinfStable.main | (intros; apply GlobalTheory.GKinfStable.main <;> assumption)
end
end
