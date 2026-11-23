module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
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
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechToDerived
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Mathlib.Data.Nat.Choose.Multinomial
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CechHStepPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.ZeroOne

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PfOmega

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem hPull_omega_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ)
    (y : Sheaf.H.{0} ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j),
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm (hPull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j y) =
      pullC u hu a j ((GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm y) := by
  intro K _ X Y q p u hu a j y
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨w, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j
    isTerminalTop).surjective y
  obtain ⟨z, rfl⟩ := (GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w
  have hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm
      (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z :=
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z
  rw [hz]
  change GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop
      (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top)
        ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm
          (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)))) =
    GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ _ j (GlobalTheory.HodgeCoh.hodgePull hu a j z))
  rw [AddEquiv.symm_apply_apply]
  congr 1

end CrystallineSemistableComparison.Om.Cech
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLift

theorem exists_injectiveSequence_lift {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') :
    ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  have hS := injectiveSequence_shortExact G
  have : Mono (injectiveSequence G).f := hS.mono_f
  have : Injective ((push f).obj (injectiveSequence G').X₂) := injective_push f _
  let τ₂ : (injectiveSequence G).X₂ ⟶ (push f).obj (injectiveSequence G').X₂ :=
    Injective.factorThru (φ ≫ (push f).map (injectiveSequence G').f) (injectiveSequence G).f
  have h₁ : (injectiveSequence G).f ≫ τ₂ = φ ≫ (push f).map (injectiveSequence G').f :=
    Injective.comp_factorThru _ _
  have h₀ : (injectiveSequence G).f ≫ τ₂ ≫ (push f).map (injectiveSequence G').g = 0 := by
    rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, (injectiveSequence G').zero,
      Functor.map_zero, comp_zero]
  let τ₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ h₀)
  have h₃ : (injectiveSequence G).g ≫ τ₃ = τ₂ ≫ (push f).map (injectiveSequence G').g :=
    Cofork.IsColimit.π_desc hS.gIsCokernel
  exact ⟨{ τ₁ := φ, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₁.symm, comm₂₃ := h₃.symm }, rfl⟩

end GlobalTheory.CompanionTheory.CechLift
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforwardStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

theorem _root_.GlobalTheory.T.injective_resolution_lift_pushforward : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G'), ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  first | exact @GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | exact GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift | (intros; apply GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.LerayClean

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem cechHEquiv_pull_compat {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) :
    ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro G G' hG hG' φ x
    exact CrystallineSemistableComparison.Om.Nt2.cechHZero_pull' f V hV U hU τ hτ φ x
  | one =>
    intro G G' hG hG' φ x
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHOne_pull' f V hV U hU τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α x
  | more m _ ih =>
    intro G G' hG hG' φ x
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHStep_pull' f V U τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α m _ _
      (fun y => ih
        (injectiveSequence_goodAcyclic hCY G hG) (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

theorem cechHEquiv_pullC : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro X Y f BY GoodY BX GoodX hCY hCX κ ι V hV hVB U hU hUB τ hτ n G G' hG hG' φ x
  exact cechHEquiv_pull_compat f hCY hCX V hV hVB U hU hUB τ hτ n hG hG' φ x

end CrystallineSemistableComparison.Om.Nt2
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.PfPullC

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech.CechFormPull

open CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOm_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x) := by
  intro K _ X Y q p u hu κ ι V hV hVaff U hU hUaff τ hτ a j x
  have h1 := CrystallineSemistableComparison.Om.Nt2.cechHEquiv_pullC u.base isCoverSystem_isBasicCover isCoverSystem_isBasicCover V hV
    (fun i => by rw [inter_eq_iInf]; exact hVaff _ i) U hU (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) τ hτ j
    (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega p a)) (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega q a))
    (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) x
  have h2 := hPull_omega_pf q p u hu a j (cechHAddEquivH V hV hVaff (GlobalTheory.HodgeCoh.Omega p a) j x)
  exact (congrArg (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm h1).trans h2

end CrystallineSemistableComparison.Om.Cech.CechFormPull
end
end
end
