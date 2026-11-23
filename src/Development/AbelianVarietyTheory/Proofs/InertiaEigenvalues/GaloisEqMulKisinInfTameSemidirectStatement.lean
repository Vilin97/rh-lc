module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversActionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInfStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.Algebra.Algebra.ZMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemKummerTowerUnramifiedOfCoversOneStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfActionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.covers_of_action' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf, (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) → k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  first | exact @GlobalTheory.BKGal.covers_of_action | exact GlobalTheory.BKGal.covers_of_action | (intros; apply GlobalTheory.BKGal.covers_of_action <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_galois_prescribed_unramified_kummer : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ (m : ZMod a) (ζ : Om l), ζ ^ e = 1 → ∃ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val) ∧ g (ϖ.seq 0) = ζ * ϖ.seq 0 := by
  first | exact @GlobalTheory.TameFrob.exists_cover | exact GlobalTheory.TameFrob.exists_cover | (intros; apply GlobalTheory.TameFrob.exists_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPowFrobenius

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobAction

open GlobalTheory.BKReal

theorem galois_pow_frobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l),
    ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val := by
  intro l hl a _ g
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hmem : ∀ y : Fq l a, Per.σF g (Fq.val l a y) ∈ resSub l a := fun y => by
    rw [mem_resSub, ← map_pow, ← map_pow, Fq.pow_card]
  let φ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) hmem
  have hφ : ∀ y, Fq.val l a (φ y) = Per.σF g (Fq.val l a y) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ _
  haveI : Fintype (Fq l a) := Fintype.ofFinite _
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { φ with
      commutes' := fun r => by
        haveI : NeZero l := ⟨hl.out.ne_zero⟩
        obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective r
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, map_natCast] }
  have hb : Function.Bijective ψ := Finite.injective_iff_bijective.1 ψ.toRingHom.injective
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod l) (Fq l a)).2
    (AlgEquiv.ofBijective ψ hb)
  have hfr : ∀ (k : ℕ) (y : Fq l a), (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod l) (Fq l a) ^ k) y =
      y ^ l ^ k := fun k y => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card,
        ← pow_mul, ← pow_succ]
  have hφz : φ z = z ^ l ^ (n : ℕ) := by
    have := congrArg (fun e : Fq l a ≃ₐ[ZMod l] Fq l a => e z) hn
    simp only [hfr] at this
    exact this.symm
  have hrank : Module.finrank (ZMod l) (Fq l a) = a := by
    have h2 := Module.card_eq_pow_finrank (K := ZMod l) (V := Fq l a)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, card_Fq] at h2
    exact (Nat.pow_right_injective hl.out.two_le h2).symm

  have key : ∀ y : OCb l, ((PreTilt.untilt (Per.σF g y) : Per.OC l) : ℂ_[l]) =
      Per.σC g ((PreTilt.untilt y : Per.OC l) : ℂ_[l]) := fun y => by
    rw [GlobalTheory.RingBasics.untilt_σF]
    exact GlobalTheory.RingIface.sigO_coe l g _
  have hu := GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz
  have hgω : g ω = ω ^ l ^ (n : ℕ) := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    have h3 := key (Fq.val l a z)
    rw [← hφ, hφz, map_pow, map_pow, SubmonoidClass.coe_pow, hu, GlobalTheory.RingBasics.σC_coe] at h3
    rw [map_pow]
    exact h3.symm
  refine ⟨((n : ℕ) : ZMod a), fun x hx => ?_⟩
  have hval : (((n : ℕ) : ZMod a)).val = n := ZMod.val_natCast_of_lt (lt_of_lt_of_eq n.2 hrank)
  rw [hval]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, zero_pow (pow_pos hl.out.pos _).ne']
  · have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
    haveI : NeZero (l ^ a - 1) := ⟨by omega⟩
    obtain ⟨k, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
    rw [map_pow, hgω, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory.FrobAction
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPowFrobeniusStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val := by
  first | exact @GlobalTheory.FrobAction.galois_pow_frobenius | exact GlobalTheory.FrobAction.galois_pow_frobenius | (intros; apply GlobalTheory.FrobAction.galois_pow_frobenius <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TameCover

section
variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l)
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

theorem galOA_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (x : OA l O) :
    galOA O (g * h) x = galOA O g (galOA O h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOA_tmul, galOA_tmul, galOA_tmul, GlobalTheory.RingBasics.σA_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def actA (γ : TameGal ↥LL.1 l e a) (f : ZMod a → A ↥(OL LL) ↥LL.1) : ZMod a → A ↥(OL LL) ↥LL.1 :=
  fun τ => ⟨ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) τ, Rot.ringAct_mem rot_A γ (fun σ => (f σ).2) τ⟩

theorem covers_mul {k k' : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hk : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hk' : Covers ↥LL.1 (thetaW a LL) ϖ k' γ') :
    Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ') := by
  intro f f'' hf''
  have h1 := hk' f (actA LL γ' f) (fun τ => rfl)
  have h2 := hk (actA LL γ' f) f'' (fun τ => by
    rw [hf'' τ, map_mul]
    rfl)
  rw [galOA_mul', h1, h2]

theorem covers_of_mem {k : GQ l} (hk : k ∈ ϖ.GfieldInf a) :
    Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) := by
  intro f f' hf'
  have : f' = f := funext fun τ => Subtype.ext (by rw [hf' τ, map_one]; rfl)
  rw [this]
  exact ϖ.galOA_iTot (thetaW a LL) ↥LL.1 hk f

theorem covers_unique {k : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hγ : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hγ' : Covers ↥LL.1 (thetaW a LL) ϖ k γ') : γ = γ' := by
  have key : ∀ f : ZMod a → A ↥(OL LL) ↥LL.1,
      ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) = ringAct γ' (fun σ => (f σ : PowerSeries ↥LL.1)) := by
    intro f
    have h := (hγ f (actA LL γ f) (fun _ => rfl)).symm.trans (hγ' f (actA LL γ' f) (fun _ => rfl))
    have h2 := ϖ.iTot_injective (thetaW a LL) ↥LL.1 h
    funext τ
    exact congrArg Subtype.val (congrFun h2 τ)
  have hs : γ.shift = γ'.shift := by
    by_contra hne
    have h := congrFun (key fun σ => if σ = 0 then 1 else 0) γ.shift
    simp only [ringAct_apply, sub_self] at h
    rw [if_neg (sub_ne_zero.2 hne)] at h
    simp at h
  have hl : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) = ((γ'.left : (↥LL.1)ˣ) : ↥LL.1) := by
    have h := congrArg (fun F => coeff 1 (F 0)) (key fun _ => uIn _)
    have hu : ((uIn (A ↥(OL LL) ↥LL.1) : A ↥(OL LL) ↥LL.1) : PowerSeries ↥LL.1) = X := rfl
    simp only [hu, ringAct_X, coeff_C_mul, coeff_one_X, mul_one] at h
    simpa [TameGal.root] using h
  refine SemidirectProduct.ext (Subtype.ext (Units.ext hl)) ?_
  exact congrArg Multiplicative.ofAdd hs

omit [HasUnr a LL] in
theorem lift_root (a : ℕ) [TameDescentExponentData ↥LL.1 l e a] (ζ : Om l) (hζ : ζ ^ e = 1) :
    ∃ ζK : rootsOfUnity e ↥LL.1, (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) = ζ := by
  obtain ⟨ζ0, h0⟩ := TameDescentExponentData.prim (K := ↥LL.1) l a (e := e)
  have h1 : IsPrimitiveRoot ((ζ0 : ↥LL.1) : Om l) e := h0.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨rootsOfUnity.mkOfPowEq (ζ0 ^ i) (by rw [← pow_mul, mul_comm, pow_mul, h0.pow_eq_one, one_pow]), ?_⟩
  rw [rootsOfUnity.val_mkOfPowEq_coe, ← hi]
  rfl

end

end GlobalTheory.TameCover
end

namespace GlobalTheory.TameCover

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  intro l _ a e _ _ ϖ LL _ _
  have hsucc : e + 1 = l ^ a := TameDescentExponentData.succ_eq (↥LL.1) (l := l) (e := e) (a := a)

  have hroot_mem : ∀ x : Om l, x ^ l ^ a = x → x ∈ (ϖ.field a).1 := fun x hx =>
    ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _ hx)
  have hfix : ∀ h ∈ GK (ϖ.field a), ∀ x ∈ (ϖ.field a).1, h x = x := fun h hh x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
  refine ⟨GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc, ?_, ?_, fun k γ γ' => covers_unique ϖ LL, fun k k' γ γ' => covers_mul ϖ LL,
    fun k => ⟨GlobalTheory.T.mem_kummerTowerUnramified_of_covers_one l a e ϖ LL k, covers_of_mem ϖ LL⟩, ?_⟩
  · intro k hk
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq l a k
    have hπ : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
    have hke : k (ϖ.seq 0 ^ e) = ϖ.seq 0 ^ e :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩)
    have hζ : (k (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, hke, div_self (pow_ne_zero _ hπ)]
    obtain ⟨ζK, hζK⟩ := lift_root LL a _ hζ
    refine ⟨⟨ζK, Multiplicative.ofAdd m⟩, GlobalTheory.T.covers_of_action' l a e ϖ LL _ k hk hm ?_⟩
    change k (ϖ.seq 0) = (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0
    rw [hζK, div_mul_cancel₀ _ hπ]
  · intro γ
    have hζ : ((((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)) ^ e = 1 := by
      have h1 : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 γ.left.2, Units.val_one]
      rw [← IntermediateField.coe_pow, h1]
      rfl
    obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.exists_galois_prescribed_unramified_kummer l a e ϖ hsucc γ.shift _ hζ
    obtain ⟨h, hh, k, hk, rfl⟩ := GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc g
    have hinj : Function.Injective h := h.injective
    refine ⟨k, hk, GlobalTheory.T.covers_of_action' l a e ϖ LL γ k hk (fun x hx => hinj ?_) (hinj ?_)⟩
    · have h1 := hg1 x hx
      have h2 : (x ^ l ^ γ.shift.val) ^ l ^ a = x ^ l ^ γ.shift.val := by
        rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [hfix h hh _ (hroot_mem _ h2)]
      exact h1
    · have hz : (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) ^ l ^ a = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
        rw [← hsucc, pow_succ, hζ, one_mul]
      rw [hfix h hh _ (mul_mem (hroot_mem _ hz) (ϖ.pi_mem_field a))]
      exact hg2
  · intro k ζ hk
    obtain ⟨hr, -⟩ := GlobalTheory.T.action_of_covers l a e ϖ LL k _ hk
    have hr' : ∀ x : Om l, x ^ l ^ a = x → k x = x := fun x hx => by
      rw [hr x hx]
      simp
    obtain ⟨k', hk', h, hh, hkh⟩ := GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf l a e ϖ hsucc k hr'
    have hc : Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) := by
      have := covers_mul ϖ LL hk (covers_of_mem ϖ LL hh)
      rwa [mul_one, ← hkh] at this
    refine ⟨k', hk', hc, ?_⟩
    rw [(GlobalTheory.T.action_of_covers l a e ϖ LL _ _ hc).2]
    rfl

end GlobalTheory.TameCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  first | exact @GlobalTheory.TameCover.main | exact GlobalTheory.TameCover.main | (intros; apply GlobalTheory.TameCover.main <;> assumption)
end
end
