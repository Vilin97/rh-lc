module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePart
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueIdempotentConjAtLevelPlaceStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DivisibilityTypeProductReadLevelPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

open scoped Pointwise

namespace GlobalTheory.SeeConjZMod

theorem dvd_of_mem_primes {A : Type} [CommRing A] [IsDedekindDomain A] {x b : A} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum A, x ∈ P.asIdeal → x ∉ P.asIdeal ^ 2 ∧ b ∈ P.asIdeal) : x ∣ b := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have hsq : Squarefree (Ideal.span {x}) := by
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
    intro p hp hd
    have hpr : Prime p := hp.prime
    let P : HeightOneSpectrum A := ⟨p, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩
    have h2 : x ∈ p ^ 2 := by
      rw [sq, ← Ideal.dvd_span_singleton]; exact hd
    exact (h P (Ideal.pow_le_self two_ne_zero h2)).1 h2
  have hrad : (Ideal.span {x}).IsRadical := by
    intro y ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsq.isRadical n _ hn
  rw [← Ideal.mem_span_singleton]
  apply hrad
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro J ⟨hJ, hp⟩
  exact (h ⟨J, hp, fun h0 => hI (le_bot_iff.1 (h0 ▸ hJ))⟩ (hJ (Ideal.mem_span_singleton_self x))).2

theorem conj_of_isConj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.L2.DIV.IsConjPl P P') :
    GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv P P' := by
  have hle : D.host.conj • P.asIdeal ≤ P'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact (hc _ y ((GlobalTheory.TypePlaces.star_eq_conj D _).trans (D.host.conj.apply_symm_apply (y : D.host.E))).symm).1 hy
  have hmax : (D.host.conj • P.asIdeal).IsMaximal := by
    have := P.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => P.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj P P').2 (hmax.eq_of_le P'.isPrime.ne_top hle)

theorem g_coprime (D : D7) :
    IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
  Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)

theorem g_not_mem_sq (D : D7) (P : Pl D.host.E) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  intro h
  rw [Nat.cast_mul] at h
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 :=
    fun k hk => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P hk).2.1
  have hno : ¬ (((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) := by
    rintro ⟨h0, h1⟩
    obtain ⟨a, b, hab⟩ := g_coprime D
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)
  have hP := P.isPrime
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal (mul_comm (_ : 𝓞 D.host.E) _ ▸ h) with h' | h'
    · exact hno ⟨h0, h'⟩
    · exact key 0 h0 h'
  · rcases Ideal.IsPrime.mul_mem_pow P.asIdeal h with h' | h'
    · exact hno ⟨h', h1⟩
    · exact key 1 h1 h'

theorem exists_eq_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (hm : m ≠ 0) (hsq : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (s : Formalism.L2.Herm.intAf F E)
    (h : ∀ P : Pl E, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal → resS F P s = 0) :
    ∃ t : Formalism.L2.Herm.intAf F E, s = (m : ℕ) * t := by
  have hm0 : ((m : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, hq⟩ := cmpS_surj (F := F) (Ideal.span {((m : ℕ) : 𝓞 E)}) (by simpa using hm0)
    (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hb : oToS F E b - s ∈ idS F (Ideal.span {((m : ℕ) : 𝓞 E)}) :=
    Ideal.Quotient.eq.1 hq
  rw [idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at hb
  obtain ⟨u, hu⟩ := hb
  have hd : ((m : ℕ) : 𝓞 E) ∣ b := by
    refine dvd_of_mem_primes hm0 fun P hP => ⟨hsq P, ?_⟩
    have e := congrArg (resS F P) hu
    rw [map_sub, h P hP, sub_zero, resS_oToS, map_mul, map_natCast] at e
    have e0 : ((m : ℕ) : kP P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hP
    rw [e0, zero_mul] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e
  obtain ⟨w, rfl⟩ := hd
  refine ⟨oToS F E w - u, ?_⟩
  rw [map_mul, map_natCast] at hu
  linear_combination -hu

theorem div_or_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (P : Pl D.host.E)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ k, Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Pb.Div k P ∨ Pb.Div k (Formalism.L2.DIV.conjPl P) := by
    intro k hk
    have h := ((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) P
      hk).2.2.2 (Pb.pb k) (Pb.pb_over k) _ (conj_of_isConj (Formalism.L2.DIV.isConjPl_conjPl P))).2
    by_contra hn
    rw [not_or] at hn
    exact hn.1 (h.2 hn.2)
  rw [Nat.cast_mul] at hP
  exact (P.isPrime.mem_or_mem hP).elim (fun h => ⟨0, key 0 h⟩) (fun h => ⟨1, key 1 h⟩)

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs _
  have hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k, R.C.P.Div k PP := hIs.Pg
  refine ⟨fun PP hPP => ?_, fun c hc hc' h => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hPP
    have ho : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ ho
    · exact Ideal.mul_mem_left _ _ ho
  · obtain ⟨t, ht⟩ := exists_eq_mul (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
      (g_not_mem_sq D) ⟨c, hc⟩ fun P hP => by
        obtain ⟨k, hk | hk⟩ := div_or_conj R.C.P P hP
        · exact (h P ((hPg P).2 ⟨k, hk⟩)).1
        · exact (resS_sigS_eq_zero_iff (II D).cm (Formalism.L2.DIV.isConjPl_conjPl P) ⟨c, hc⟩).1
            (h _ ((hPg _).2 ⟨k, hk⟩)).2
    refine ⟨t.1, t.2, ?_⟩
    have e := congrArg Subtype.val ht
    rw [Subring.coe_mul, Subring.coe_natCast] at e
    exact e

end GlobalTheory.SeeConjZMod
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DivisibilityTypeProductReadLevelPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.divisibility_typeProduct_read_levelPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  first | exact @GlobalTheory.SeeConjZMod.main | exact GlobalTheory.SeeConjZMod.main | (intros; apply GlobalTheory.SeeConjZMod.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.finiteMatrix_iota_eq_finitePart : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  first | exact @GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | exact GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | (intros; apply GlobalTheory.SeeConjGroup.fmat_iota_eq_finE <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.local_frame_hermitian_ideal : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (Pg : Finset (Pl D.host.E)), IsFrame β (II D).L → (∀ PP ∈ Pg, ∃ w : Bool, LocAt g e0 f0 z0 bw bwd ew β PP w) → (∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) g c) → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → (∀ PP ∈ Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) → K2cong (II D) g e0 z0 bw x := by
  first | exact @GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym | exact GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym | (intros; apply GlobalTheory.SeeConjGroup.Bwd.k2cong_of_unipSym <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred κ hK hS
  classical
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hFH : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew :=
    ⟨vectorsInLattice, gramIntegral, formsAtZero, weightVectorsIntegral, ew_orth, bw_w, bwd_w, bw_dual, latticeSpan⟩
  obtain ⟨hgP, hZ⟩ := GlobalTheory.T.divisibility_typeProduct_read_levelPlaces R F hIs hGrp
  have hL : (II D).L = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    ext x
    refine (Formalism.L2.SG.InstExistsPf.mem_Lv D x).trans ?_
    simp only [Formalism.L2.Herm.crdLat, Formalism.L2.Herm.crd]
    constructor
    · intro hx
      refine ⟨(VS D).frame.equivFun.symm x, ?_, (VS D).frame.equivFun.apply_symm_apply x⟩
      have e := Module.Basis.equivFun_symm_apply (VS D).frame x
      rw [← e] at hx
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change (VS D).frame.equivFun y = x at hyx
      rw [← hyx, (VS D).frame.sum_equivFun y]
      exact hy
  have hβ' : IsFrame β (II D).L := by rw [hL]; exact hβ
  have hloc : ∀ PP ∈ R.Pg, ∃ w : Bool,
      LocAt (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew β PP w := by
    intro PP hP
    obtain ⟨h1, h2, hA1, hA0⟩ := GlobalTheory.T.residue_idempotent_conj_at_levelPlace (D.host.g 0 * D.host.g 1) ew ew_idem ew_orth ew_int ew_full PP (hgP PP hP)
    have hr : RedIs β PP (if GlobalTheory.StdFrames.cpt PP ew = 1 then
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0
      else flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hred PP hP
    by_cases hc : GlobalTheory.StdFrames.cpt PP ew = 1
    · rw [if_pos hc] at hr
      exact ⟨true, hgP PP hP, fun _ => by simpa using (hA1 hc).1, fun _ => by simpa using (hA1 hc).2, hr⟩
    · rw [if_neg hc] at hr
      exact ⟨false, hgP PP hP, fun _ => by simpa using (hA0 hc).1, fun _ => by simpa using (hA0 hc).2, hr⟩
  have hxM : (II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := GlobalTheory.T.finiteMatrix_iota_eq_finitePart κ
  show _ ∧ _ ↔ _
  constructor
  · rintro ⟨-, hc⟩ PP hP
    obtain ⟨w, hw⟩ := hloc PP hP
    exact GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent _ e0 f0 z0 bw bwd ew hFH β PP w hβ' hw _ (finE (Yc D 0) κ) hK hxM hS hc
  · intro hu
    exact ⟨hK, GlobalTheory.T.local_frame_hermitian_ideal _ e0 f0 z0 bw bwd ew hFH β R.Pg hβ' hloc hZ _ (finE (Yc D 0) κ) hK hxM hS hu⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | exact GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent | (intros; apply GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent <;> assumption)
end
end
