module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZeroStatement
public import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
public import Development.AutomorphicArithmetic.ResidueCharacters.LocRes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
public import Development.AutomorphicArithmetic.ResidueCharacters.TbKOf
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistDef
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfLocallyConstant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemGKChiPowNeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaTmulOneMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatumStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.crysOnCond_of_every_datum : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F := by
  first | exact @GlobalTheory.crysOnCond_all | exact GlobalTheory.crysOnCond_all | (intros; apply GlobalTheory.crysOnCond_all <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomic

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem invariants_killed_over_cyclotomic_subfield_of_admissible (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hH0 : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (M0 h0 : ℕ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      LocalSituation.HypW (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie T M0 h0 →
      (∀ τ, ¬ IsJumpV ((D.loc l).PD K) T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) →
      ((((D.loc l).PD K).p : ↥(OL LL)) ^ LocalSituation.cLL l (LocalSituation.mN l s (M0 + h0))
        (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l s (M0 + h0)))) - padicValNat l (Module.finrank ℚ_[l] ↥K.1))
        (LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) T) 0 1) • x = 0)
    (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : InvariantsKilledOverCyclotomic (D.loc l) := by
  intro N h n K LL hC T U hn hb hc hj h0 x hx
  obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
  have hle : GK K' ≤ GK K := GK_le hKK
  obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle T hc
  have hsub := LocRes.jset_sub D HW hres hF hKK hle hg T hc U hj
  have hWT := hW K' _ LL hg (LocRes.res hle T) h h r1 fun a ha => hb a (hsub ha)
  have hk := hH0 K' _ LL hg h h (LocRes.res hle T) hWT (fun τ hτ => h0 _ ((j1 τ 0).1 hτ)) x fun g => hx _
  have hvd := LocRes.vdeg_le K' (s := sN l N) (m := LocalSituation.mN l (sN l N) (h + h))
    (le_max_left _ _) (by unfold LocalSituation.mN; omega)
  rw [hKs] at hvd
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (LocNum.latticeExponent_one_le_invariantsKillingExponent l N h n _ Fact.out U _ hsub hn hb hvd)
  rw [(D.loc l).PD_p] at hk
  rw [hd, pow_add, mul_comm, mul_smul]
  erw [hk]
  exact smul_zero _

end UpperTheory.N

end
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.LiftKOf

section

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

theorem liftK_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32) (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL)) : LiftK (D.loc l) := by
  intro N h K LL hC T₁ T₂ f hc1 hc2 hon hj
  obtain ⟨K', hKK, hg, hKs, hnor, hidx⟩ := LocNum.exists_up hC
  have hle : GK K' ≤ GK K := GK_le hKK
  have hrn : (Subgroup.inclusion hle).range.Normal := by
    rw [Subgroup.inclusion_range]; exact hnor.subgroupOf _
  have hB := LocRes.caseB (D.loc l) (HW l) hg hKs
  obtain ⟨r1, j1⟩ := LocRes.res_crys D.loc hres hF hKK hle T₁ hc1
  obtain ⟨r2, -⟩ := LocRes.res_crys D.loc hres hF hKK hle T₂ hc2
  have hJ : LiftingTheory.JumpsLet ((HW l).W K' _ LL hg) (LocRes.res hle T₁) (fun _ => h) (fun _ => h) :=
    fun _ τ _ a ha => hj _ a ((j1 τ a).1 ha)
  have h1 := ((h54.2.2.2.2 l K' K hKK hle (hnor.subgroupOf _) _ LL hg).1 hrn T₁ T₂ f (fun _ => h) (fun _ => h)
    ⟨r1, r2, hon⟩ hJ).2 hB
  have h2 := (h54.2.2.2.1 l K' _ LL hg (LocRes.res hle T₁) (fun _ => h) (fun _ => h) r1 hJ).2.1 hB
  refine LiftF_mono _ f ?_ h1
  have hH := Hmax_const_le (Module.finrank ℚ_[l] ↥(K0 K')) h h
  rw [(HW l).W_s] at h2 ⊢
  rw [(D.loc l).PD_p] at h2 ⊢
  have h3 : LiftingTheory.ePB l (sN l N) (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h) (LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) fun _ => h)
      (LiftingTheory.jumpSet ((HW l).W K' (sN l N) LL hg) (LocRes.res hle T₁)
        (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h) (LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K')) fun _ => h)) ≤
      32 * (LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) (fun _ => h) * sN l N + 1) := by
    exact_mod_cast h2
  have h4 : LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K')) (fun _ => h) (fun _ => h) * sN l N ≤
      2 * h * sN l N := Nat.mul_le_mul_right _ (by omega)
  refine (Nat.add_le_add h3 hidx).trans ?_
  unfold eL lamN
  omega

end UpperTheory.N

end
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.TwistK

section

@[expose] public section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct GlobalTheory.TwistTors

namespace UpperTheory.N.TwistK

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem tbe_of (PD : PeriodData G Qp K₀ K B BdR) (I : Subgroup G) [TopologicalSpace Qp] [CompactSpace G] [IsTopologicalGroup G]
    [IsTopologicalRing LL] (hO : GoodO (Qp := Qp) LL O)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {((PD.p : ℕ) : O) ^ n}))
    (hp : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : TateFilteredInvariants PD) (h7 : fontCore PD) (hbk : bkADim PD)
    (heul : ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, PD.p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (Module.finrank Qp K + 2))
    (hchi : ∀ e : ℕ, 0 < e → ∃ g : G, (PD.χ g : Qp) ^ e ≠ 1)
    (φ : G) (hφ : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤)
    (δ : G → LL) (hδ : δ ∈ finiteCocycles PD (1 : Representation LL G LL))
    (hδI : ∀ g ∈ I, δ g = 0) (hδ0 : δ ≠ 0) : TBe PD LL O I := by
  intro e Ve h1 hχ
  obtain ⟨hDR, hFil⟩ := GlobalTheory.isDR_and_DdR_le_Fil_zero_of_twist PD Ve.ρ e hχ
  have hpos : 0 < e → HfD PD Ve.L = BD Ve.L ∧ BD Ve.L ≠ ⊥ := by
    intro he
    obtain ⟨g, hg1⟩ := hchi e he
    have hu : ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one, ← map_pow, map_eq_one_iff _ (algebraMap Qp LL).injective]
      exact hg1
    exact ⟨HfD_eq_BD PD Ve (GlobalTheory.HfZero.z1f_le_b1 PD h5 h7 hO (toG Ve) hDR hFil
      (fixed_points_trivial_of_scalar_action_ne_one Ve _ _ hu (hχ _))), BD_ne_bot hO Ve h1 _ _ hu (hχ _)⟩
  have hzero : e = 0 → HfD PD Ve.L ≠ ⊥ ∧ ∀ c : G → Ve.V ⧸ Ve.L.T, c ∈ HfD PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ I, c g = actD Ve.L g x - x) := by
    rintro rfl
    simp only [pow_zero, one_smul] at hχ
    have htop : H0V Ve.ρ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (Submodule.mem_iInf _).2 fun g => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hχ, LinearMap.id_apply, sub_self]
    have hdim : ((Module.finrank LL (FiniteCohomology PD Ve.ρ) : ℕ) : ℤ) =
        Module.finrank LL ↥(H0V Ve.ρ) + ((Module.finrank LL ↥(DdR PD Ve.ρ) : ℤ) -
          Module.finrank LL ↥(DdR PD Ve.ρ ⊓ FilV PD (LL := LL) (V := Ve.V) 0)) :=
      hbk _ _ hO (toG Ve) hDR
    rw [inf_eq_left.2 hFil, sub_self, add_zero, htop, finrank_top, h1] at hdim
    exact GlobalTheory.UnramifiedClasses.HfD_eq_unramified PD hO Ve h1 hχ (by exact_mod_cast hdim) I φ hφ δ hδ hδI hδ0
  refine ⟨fun n => ?_, fun he => (hpos he).1, fun he => (hzero he).2⟩
  have hne : HfD PD Ve.L ≠ ⊥ := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exact (hzero he).1
    · rw [(hpos he).1]; exact (hpos he).2
  haveI := hfin n
  haveI : IsDomain O := hO.1.1
  have key := len_part PD hO Ve h1 PD.p n (Module.finrank Qp K) (pow_ne_zero n hp)
    (heul n) hne
  have hord : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O) ^ n}) =
      n • Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hp) n
  unfold lenOl
  rw [Nat.cast_mul, mul_assoc, ← nsmul_eq_mul n, ← hord]
  exact key

end

theorem tbe_all (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hA : admitted D HW F) (hB : Conclusion5 D)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) : TBe ((D.loc l).PD K) ↥LL.1 ↥(OL LL) (IK K) := by
  obtain ⟨-, hA2, -, hA4, hA5, -, hA7, -, -⟩ := hA
  obtain ⟨hO, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  haveI := K.2
  haveI hc : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨δ, hδ, hδI, hδ0⟩ := exists_unr D l K LL
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  haveI : IsTopologicalRing ↥LL.1 := hO.2.2.2.1
  refine tbe_of _ _ hO ?_ ?_ (hA5 l K) (hA7 l K) (hB l K).2.1 ?_ ?_ φ hφ δ hδ hδI hδ0
  · rw [hp]; exact hfin
  · rw [hp]; exact hl0
  · rw [hp]; exact GlobalTheory.CocycleCount.cocycles_finite_ncard_le hA2 hA4 l K
  · intro e he
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.Cyc.exists_mem_GK_chi_pow_ne_one l (D.loc l).χQ (D.loc l).χQ_cyc K e he
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [(D.loc l).PD_χ K ⟨g, hg⟩]
    exact hg1

end UpperTheory.N.TwistK

end
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.LocAllOf

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

theorem UpperTheory.N.locAll_of (hbk : GlobalTheory.Published.BlochKatoLocal) (htd : Formalism.GaloisCohomology.LocalTateDualityK)
    (hec : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie) :
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) := by
  have hres : ElementDenominator.CrystallineRestrictionToExtension D.loc := GlobalTheory.T.crystalline_restrict_finite_extension_jumps D
  have hF := GlobalTheory.FontaineAll.fontaineAt_all D l
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler htd hec D HW F
  exact ⟨UpperTheory.N.liftK_of D HW F l h54 hres hF,
    UpperTheory.N.invariants_killed_over_cyclotomic_subfield_of_admissible D HW F l hW (fun K s LL h => GlobalTheory.T.torsion_exponent_kills_invariants_of_good hbk htd hec D HW F Cm l K s LL h) hres hF,
    UpperTheory.N.tbK_of D HW F l (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hbk htd hec D HW F Cm) (GlobalTheory.T.crysOnCond_of_every_datum D HW F) hW
      (UpperTheory.N.TwistK.tbe_all D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hbk htd hec D) l) hres hF⟩
end
end

-- Source module: Development.AutomorphicArithmetic.ResidueCharacters.LocAll

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.locAll : Hypotheses₂ → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime],
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) :=
  fun hP D HW F Cm l _ => UpperTheory.N.locAll_of hP.bk hP.tate hP.euler D HW F Cm l
    (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2 (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm l)
end
end
