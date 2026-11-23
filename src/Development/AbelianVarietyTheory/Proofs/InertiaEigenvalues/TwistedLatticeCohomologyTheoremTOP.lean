module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleUntwistedCharUnramifiedOfResidueRealis
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.BasicDefinitions.AdRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharUnramified
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCore
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentAdmissibleCocyclesResidue
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModThOfPres
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPresTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StmtOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictnessOfTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToAmbCoefH1EqCoefAmbToAmb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishOfLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmittedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormula

section

@[expose] public section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.EulerFree

theorem card_Z1_of_invariants_eq_bot {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥) :
    Nat.card (ReciprocityTheory.Def.Z1 π ⊤) = Nat.card (ReciprocityTheory.Def.H1 π ⊤) * Nat.card M := by
  have hle : ReciprocityTheory.Def.B1 π ⊤ ≤ ReciprocityTheory.Def.Z1 π ⊤ := by
    rintro _ ⟨m, -, rfl⟩
    refine ⟨⟨(hlc m).comp (fun x => x - m), fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    change π x.1 (π x.2 m - m) - (π (x.1 * x.2) m - m) + (π x.1 m - m) = 0
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤))
  have h2 : Nat.card ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤)) =
      Nat.card (ReciprocityTheory.Def.B1 π ⊤) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hinj : Function.Injective (ReciprocityTheory.Def.d0 π) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← h0]
    intro m hm g
    exact sub_eq_zero.1 (congrFun (LinearMap.mem_ker.1 hm) g)
  have h3 : Nat.card (ReciprocityTheory.Def.B1 π ⊤) = Nat.card M :=
    (Nat.card_congr (Submodule.topEquiv.symm.trans
      (Submodule.equivMapOfInjective _ hinj ⊤)).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem card_H1_of_euler (R O G G' : Type) [CommRing R] [CommRing O] [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (π : Representation O G' M) (ha : ∀ g m, rho g m = π (φ.symm g) m)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥)
    (h2 : Subsingleton (ReciprocityTheory.Def.H2 π ⊤)) :
    Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ d := by
  have ha' : ∀ g m, rho (φ g) m = π g m := fun g m => by rw [ha, φ.symm_apply_apply]
  have hH0 : Nat.card (ReciprocityTheory.Gal.H0 rho) = 1 := by
    have : ReciprocityTheory.Gal.H0 rho = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ π.invariants := fun g => by rw [← ha']; exact hm (φ g)
      rw [h0] at this
      exact this
    rw [this]
    exact Nat.card_unique
  have hH2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = 1 := by
    have : Subsingleton (ReciprocityTheory.Gal.H2 rho) := by
      refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun z _ => ?_)
      let z' : ReciprocityTheory.Def.Z2 π ⊤ := ⟨fun x => z.1 (φ x.1, φ x.2),
        ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp
          ((hφ.1.comp continuous_fst).prodMk (hφ.1.comp continuous_snd))), fun _ => Submodule.mem_top⟩, by
        funext x
        have := z.2.2 (φ x.1) (φ x.2.1) (φ x.2.2)
        rw [ha', ← map_mul, ← map_mul] at this
        exact this⟩
      have hz' : z' ∈ (ReciprocityTheory.Def.B2 π ⊤).submoduleOf (ReciprocityTheory.Def.Z2 π ⊤) := by
        rw [Submodule.Quotient.subsingleton_iff.1 h2]
        exact Submodule.mem_top
      obtain ⟨b, hb, hbz⟩ := hz'
      refine ⟨fun g => b (φ.symm g), hb.1.continuous.comp hφ.2, ?_⟩
      funext x
      have h : π (φ.symm x.1) (b (φ.symm x.2)) - b (φ.symm x.1 * φ.symm x.2) + b (φ.symm x.1) =
          z.1 (φ (φ.symm x.1), φ (φ.symm x.2)) := congrFun hbz (φ.symm x.1, φ.symm x.2)
      rw [φ.apply_symm_apply, φ.apply_symm_apply, ← map_mul, ← ha] at h
      exact h
    exact Nat.card_unique
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  let E : ↥(ReciprocityTheory.Def.Z1 π ⊤) ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, cocycle_mul]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        ⟨(IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun _ => Submodule.mem_top⟩, by
          funext x
          have := c.2.2 (φ x.1) (φ x.2)
          rw [ha', ← map_mul] at this
          change π x.1 (c.1 (φ x.2)) - c.1 (φ (x.1 * x.2)) + c.1 (φ x.1) = 0
          rw [this]
          abel⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hM : 0 < Nat.card M := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hM
  rw [← card_Z1_of_invariants_eq_bot π hlc h0, Nat.card_congr E]
  rw [hEu, hH0, hH2] at hZ
  simpa using hZ

theorem card_H1_eq_pow :
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  intro hE l _ K O M _ _ _ _ π hl hlc h0 h2
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ 1 • m = 0 := fun m => by rw [pow_one, hl]
  have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => (π (φ.symm g)).toAddMonoidHom)
      (fun m => by simp) (fun g h m => by simp)
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  exact card_H1_of_euler _ O _ _ φ hφ M rho hrho _ (hE l K.1 hK 1 M rho Nat.one_pos hrho) π
    (fun _ _ => rfl) hlc h0 h2

end GlobalTheory.EulerFree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormulaStatement

section

@[expose] public section

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.card_H1_local_euler_formula : Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  first | exact @GlobalTheory.EulerFree.card_H1_eq_pow | exact GlobalTheory.EulerFree.card_H1_eq_pow | (intros; apply GlobalTheory.EulerFree.card_H1_eq_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCoreStatement

section

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem _root_.GlobalTheory.T.exactLocalConditions_topCore : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  first | exact @GlobalTheory.TopDict.topCore_of_typings | exact GlobalTheory.TopDict.topCore_of_typings | (intros; apply GlobalTheory.TopDict.topCore_of_typings <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedLatticeCohomologyTheoremTOP

section

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open GlobalTheory.PhiGam GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopBridge

theorem freeH_of_vanish_euler : Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Vanish → S.FreeH := by
  intro heul l _ P S hV
  obtain ⟨hs, ht, -, -, -⟩ := S.hyp
  obtain ⟨hDVR, -, -, hA, hF, hFr⟩ := GlobalTheory.CoefInt.integers_laws l S.LL
  haveI := hDVR
  haveI := hFr
  exact GlobalTheory.FreeCoh.free_and_tensIso_gal S.Γ hs.2.2.2.2.2 hA hF
    (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (fun U hU => GlobalTheory.FreeCoh.pow_mul_mem_nhds S.LL S.Γ.lam hs.2.2.2.2.2 U hU)
    ht.2.2.1.1 (GlobalTheory.AdmClasses.not_isUnit_integers l S.LL) hV.1 hV.2 ht.1 hs.2.2.1
    (fun M _ _ _ π hlm hlc h0 h2 => GlobalTheory.T.card_H1_local_euler_formula heul l S.K S.O M π hlm hlc h0 h2)

theorem stmtAt_of_real (hdual : Formalism.GaloisCohomology.LocalTateDualityK) (heul : Formalism.GaloisCohomology.LocalEulerCharK)
    {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (htied : Nonempty (LocTied l P AI))
    (hreal : ∀ S : TopSit P, S.Real)
    (hbk : ∀ K LL : FinExt l, CaseA K LL → tableLineDegreeTwo.BlochKatoJumpDimension (P.PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (IK K)) :
    GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P := by
  intro K LL n r _ emb D Γ hs ht h1 h2 h3
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, ⟨hs, ht, h1, h2, h3⟩⟩
  have hCC : S.CrysCalc := GlobalTheory.TopSteps.CrysRules.crysCalc AI htied S
  have hR : S.Real := hreal S
  have hV : S.Vanish := GlobalTheory.TopVanish.vanish_of_real hdual S hR
  have hF : S.FreeH := freeH_of_vanish_euler heul S hV
  have hCl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hStd : S.StdAdm := GlobalTheory.TopSteps.StdAdm.stdAdm S hCC hCl
  have hL0 : S.Lem0 S.Γ.W₀ := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl hStd).1
  have hFS : S.FSummand :=
    GlobalTheory.TopSteps.FinSummandJumps.fSummand S (hbk K LL hs.2.1) hCC hV hF
  have hFA : S.FinAdm :=
    GlobalTheory.FiniteAdm.finAdm S hCC (GlobalTheory.FontaineExtensionCriteria.extCrys_of_tied P AI htied) hCl hStd hL0
  have hPsi : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi := GlobalTheory.PsiShiftProof.lemmaPsi
  have hRB : S.ResBound S.Γ.W₀ S.D.dsum := GlobalTheory.ResidueBound.resBound_dsum hPsi S hR hL0
  refine ⟨hV.1, hV.2, hF.1, hFS, fun X _ _ _ => ⟨hF.2 X, ?_⟩⟩
  exact GlobalTheory.AdmFinite.cls_eq_H1fX S hL0 hF hFS hFA hRB X

theorem twistedLatticeCohomology_theoremTOP : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.Stmt D HW F Cm := by
  intro D HW F Cm hA l _ K LL hK lam hlam
  have htied : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  have h18 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h19 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hreal : ∀ S : TopSit (D.loc l), S.Real := fun S =>
    GlobalTheory.BasePairs.real_of_presented (D.locA l) (HW l) (F l) S
      (GlobalTheory.RedFun.realD (D.locA l) (HW l) (F l) S)
      (GlobalTheory.T.wachLattice_usedProperties_of_admitted D HW F Cm hA l S.K S.LL S.hyp.1.2.1)
      (GlobalTheory.TopSteps.CrysRules.crysCalc (D.locA l) htied S)
  exact GlobalTheory.T.exactLocalConditions_topCore (D.loc l) (D.locA l) htied (HW l)
    (stmtAt_of_real h18.1 h18.2 (D.loc l) (D.locA l) htied hreal (fun K' LL' hc => h19 l K' LL' hc))
    (GlobalTheory.TopSteps.CharVanish.stmt_of_real (D.loc l) (D.locA l) htied hreal)
    (GlobalTheory.TopSteps.admissibleUntwistedCharUnramified_of_residueRealisation (D.loc l) (D.locA l) htied hreal)
    K LL hK lam hlam

end GlobalTheory.TopBridge
end
end
