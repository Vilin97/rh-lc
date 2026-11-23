module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcrisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegreeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.crystalline_character_jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  first | exact @GlobalTheory.Per.CharJumps.jumps_of_exact_degree | exact GlobalTheory.Per.CharJumps.jumps_of_exact_degree | (intros; apply GlobalTheory.Per.CharJumps.jumps_of_exact_degree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectors

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LetterCrys

theorem isCrys_of_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  intro l _ P AI hT K LL hA μ hμ d hw
  haveI := LL.2
  haveI := K.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := charRep μ
      cont := fun x => (hμ.mul continuous_const :
        Continuous fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x) }
  obtain ⟨⟨hfin, hle⟩, -, -⟩ :=
    GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K ↥LL.1 ↥(OL LL) hgood A
  haveI : Module.Finite ↥LL.1 ↥(Dcris (P.PD K) (charRep μ)) := hfin
  unfold IsCrys
  refine le_antisymm hle ?_
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 :=
    Formalism.MainNotions.N.JsetEmb.card_emb_good hA.2.2
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  have hfr : finrank ℚ_[l] ↥(K0 K) = finrank ℚ_[l] ↥K.1 :=
    (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) := fun x =>
    ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  let f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) := fun τ =>
    τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
  have hf : Function.Injective f := fun τ τ' h => AlgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    exact AlgHom.congr_fun h y
  choose w hwmem hw1 hw2 using hw
  have hne : ∀ τ, w τ ≠ 0 := fun τ h0 => hw2 τ (by rw [h0, map_zero]; exact Submodule.zero_mem _)
  have hind : iSupIndep fun τ => DcrisL (P.PD K) (charRep μ) (f τ) :=
    (GlobalTheory.NL.PhiD.iSupIndep_letter (P.PD K) (charRep μ)).comp hf
  have hli : LinearIndependent ↥LL.1 w := iSupIndep.linearIndependent _ hind hwmem hne
  let w' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ↥(Dcris (P.PD K) (charRep μ)) := fun τ => ⟨w τ, (hwmem τ).1⟩
  have hli' : LinearIndependent ↥LL.1 w' :=
    LinearIndependent.of_comp (Dcris (P.PD K) (charRep μ)).subtype hli
  have hpos : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≠ 0 := by
    rw [hcard]; exact Module.finrank_pos.ne'
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Nat.finite_of_card_ne_zero hpos
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  have h2 := hli'.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  rw [Module.finrank_self, mul_one, hfr]
  exact h2

end GlobalTheory.LetterCrys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectorsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.isCrys_character_of_crystalline_vectors : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  first | exact @GlobalTheory.LetterCrys.isCrys_of_letters | exact GlobalTheory.LetterCrys.isCrys_of_letters | (intros; apply GlobalTheory.LetterCrys.isCrys_of_letters <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.HWL

theorem charRep_crys_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀ x hx _hφn hF1 hF2 hφj c hc μ hcont hμ
  let ι0 := IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1
  have hsurj : Function.Surjective ι0 := fun y =>
    ⟨⟨y.1, IntermediateField.mem_inf.2 ⟨y.2, hA.1 y.2⟩⟩, Subtype.ext rfl⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.exists_letters l P K 1 LL hA.2.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by haveI := (P.PD K).finK₀; exact Module.finrank_pos.ne'⟩
  have hit : ∀ (j : ℕ) (i : ZMod (finrank ℚ_[l] ↥(K0 K))) (a : ↥(K0 K)),
      emb i ((⇑(P.PD K).σ)^[j] a) = emb (i - j) a := by
    intro j
    induction j with
    | zero => intro i a; simp
    | succ j ih =>
      intro i a
      rw [Function.iterate_succ_apply, ih]
      have h := DFunLike.congr_fun (hemb (i - j - 1)) a
      rw [sub_add_cancel] at h
      rw [AlgHom.comp_apply] at h
      rw [h]
      congr 1
      push_cast
      ring_nf
  obtain ⟨i₀, hi₀⟩ := hbij.2 (τ₀.comp ι0)
  have hμ' : ∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * (τ₀.comp ι0) ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1 :=
    fun g => hμ g
  have key : ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp ι0),
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (if τ = τ₀ then 1 else 0) ∧
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) ((if τ = τ₀ then 1 else 0) + 1) := by
    intro τ
    obtain ⟨i, hi⟩ := hbij.2 (τ.comp ι0)
    have hj : ∀ a : ↥(K0 K), (τ.comp ι0) ((⇑(P.PD K).σ)^[(i - i₀).val] a) = (τ₀.comp ι0) a := by
      intro a
      rw [← hi, ← hi₀, hit, ZMod.natCast_zmod_val, sub_sub_cancel]
    by_cases hτ : τ = τ₀
    · subst hτ
      have h0 : (i - i₀).val = 0 := by
        rw [hbij.1 (hi.trans hi₀.symm), sub_self, ZMod.val_zero]
      rw [h0] at hj
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ.comp ι0) (τ.comp ι0) 0 hμ' hj 1
        (by simpa using hF1) (by simpa [show (1 : ℤ) + 1 = 2 by norm_num] using hF2)
      simpa using this
    · have hpos : 0 < (i - i₀).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        rw [ZMod.val_eq_zero, sub_eq_zero] at h0
        subst h0
        apply hτ
        have hc' : τ.comp ι0 = τ₀.comp ι0 := hi.symm.trans hi₀
        refine AlgHom.ext fun y => ?_
        obtain ⟨z, rfl⟩ := hsurj y
        exact DFunLike.congr_fun hc' z
      have hlt : (i - i₀).val < finrank ℚ_[l] ↥(K0 K) := ZMod.val_lt _
      obtain ⟨h1, h2⟩ := hφj _ hpos hlt
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ₀.comp ι0) (τ.comp ι0) (i - i₀).val hμ' hj 0
        h1 (by simpa using h2)
      simpa [hτ] using this
  have hcrys := GlobalTheory.T.isCrys_character_of_crystalline_vectors l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key
  exact ⟨hcrys, GlobalTheory.T.crystalline_character_jumps_of_exact_degree l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key hcrys⟩

end GlobalTheory.HWL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbeddingStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.crystalline_character_jump_one_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.HWL.charRep_crys_jump_one | exact GlobalTheory.HWL.charRep_crys_jump_one | (intros; apply GlobalTheory.HWL.charRep_crys_jump_one <;> assumption)
end
end
