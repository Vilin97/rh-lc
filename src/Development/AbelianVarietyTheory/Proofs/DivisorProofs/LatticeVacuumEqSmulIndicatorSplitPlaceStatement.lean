module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatrices
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelIntertwinerGoodSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuumStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupportedStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatricesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    IsOpen (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) → IsCompact (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) →
    ∃ (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)),
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) ↔ P.val * Y ∈ matLat (Fin a') Λ := by
  first | exact @GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | exact GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | (intros; apply GlobalTheory.VacShapeCl.closure_Sa_eq_matLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMemStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.latticePairingTrivialMatrices_sub_mem : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  first | exact @GlobalTheory.VacShapeBd.bd_sub | exact GlobalTheory.VacShapeBd.bd_sub | (intros; apply GlobalTheory.VacShapeBd.bd_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatricesInvariantSupportedEqSmul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SBClosure

open scoped Topology

theorem nonarch_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup (G i)),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

theorem eq_smul_indicator_closure {X : Type} [AddCommGroup X] [TopologicalSpace X] [NonarchimedeanAddGroup X]
    (S : AddSubgroup X) (B : Set X) (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hf0 : f ≠ 0) (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB X, (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) → ∃ c : ℂ, g = c • f) :
    ∃ c : ℂ, f = c • (closure (S : Set X)).indicator 1 ∧ IsOpen (closure (S : Set X)) ∧
      IsCompact (closure (S : Set X)) := by
  set H : AddSubgroup X := S.topologicalClosure with hHdef
  have hHc : (H : Set X) = closure (S : Set X) := rfl
  rw [← hHc]
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (funext h)
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ GlobalTheory.WeilM.SB X, U.indicator φ ∈ GlobalTheory.WeilM.SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hSH : S ≤ H := S.le_topologicalClosure
  have hHcl : IsClosed (H : Set X) := S.isClosed_topologicalClosure
  have hH : ∀ h ∈ H, f (Y₀ + h) = f Y₀ := by
    intro h hh
    have hcl : IsClosed {h : X | f (Y₀ + h) = f Y₀} :=
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
    have hS : (S : Set X) ⊆ {h : X | f (Y₀ + h) = f Y₀} := fun s hs => hinv s hs Y₀
    exact (closure_minimal hS hcl) hh
  have hW : ∀ x, f x ≠ 0 → x - Y₀ ∈ H := by
    intro x hx
    by_contra hxH
    have hopen : (H : Set X)ᶜ ∈ 𝓝 (x - Y₀) := hHcl.isOpen_compl.mem_nhds hxH
    have h0 : (fun u => x - Y₀ + u) ⁻¹' (H : Set X)ᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      simpa using hopen
    obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    set V : AddSubgroup X := H ⊔ U.toAddSubgroup with hVdef
    have hVo : IsOpen (V : Set X) := AddSubgroup.isOpen_mono (le_sup_right : U.toAddSubgroup ≤ V) U.isOpen
    have hVc : IsClosed (V : Set X) := AddSubgroup.isClosed_of_isOpen V hVo
    have hxV : x - Y₀ ∉ V := by
      intro hm
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hm
      have hb' : -b ∈ U := U.neg_mem hb
      have := hU hb'
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at this
      apply this
      rw [← hab]
      simpa using ha
    set Wset : Set X := (fun y => y - Y₀) ⁻¹' (V : Set X) with hWdef
    have hWc : IsClopen Wset :=
      ⟨hVc.preimage (continuous_id.sub continuous_const), hVo.preimage (continuous_id.sub continuous_const)⟩
    have hWinv : ∀ s ∈ S, ∀ Y, (Y + s ∈ Wset ↔ Y ∈ Wset) := by
      intro s hs Y
      have hsV : s ∈ V := AddSubgroup.mem_sup_left (hSH hs)
      simp only [Wset, Set.mem_preimage, SetLike.mem_coe]
      rw [show Y + s - Y₀ = (Y - Y₀) + s by abel]
      exact V.add_mem_cancel_right hsV
    obtain ⟨c, hc⟩ := huniq (Wset.indicator f) (hind _ hWc f hf) (by
      intro s hs Y
      by_cases hY : Y ∈ Wset
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem ((hWinv s hs Y).mpr hY), hinv s hs Y]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY ((hWinv s hs Y).mp h))]) (by
      intro Y hY
      by_cases h : Y ∈ Wset
      · rw [Set.indicator_of_mem h, hsupp Y hY]
      · rw [Set.indicator_of_notMem h])
    have e1 := congrFun hc Y₀
    have e2 := congrFun hc x
    have hY₀W : Y₀ ∈ Wset := by simp [Wset, V.zero_mem]
    rw [Set.indicator_of_mem hY₀W] at e1
    rw [Set.indicator_of_notMem (show x ∉ Wset from hxV)] at e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have hc1 : c = 1 := by
      have : (c - 1) * f Y₀ = 0 := by rw [sub_mul, ← e1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hY₀)
    rw [hc1, one_mul] at e2
    exact hx e2.symm
  have hHeq : (H : Set X) = (fun h => Y₀ + h) ⁻¹' {y | f y ≠ 0} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hh; rw [hH h hh]; exact hY₀
    · intro hne; simpa using hW _ hne
  have hHo : IsOpen (H : Set X) := by
    rw [hHeq]
    exact (isOpen_compl_singleton.preimage hcont).preimage (continuous_const.add continuous_id)
  have hHk : IsCompact (H : Set X) := by
    have hK : IsCompact ((fun h => Y₀ + h) ⁻¹' tsupport f) :=
      (Homeomorph.addLeft Y₀).isCompact_preimage.mpr hf.2
    refine hK.of_isClosed_subset hHcl ?_
    intro h hh
    exact subset_tsupport f (by rw [Function.mem_support, hH h hh]; exact hY₀)
  have hHclo : IsClopen (H : Set X) := ⟨hHcl, hHo⟩
  have h1SB : (H : Set X).indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
    refine ⟨?_, HasCompactSupport.intro' hHk hHcl fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant X ℂ) hHclo).isLocallyConstant
    convert this using 1
    funext x
    first
    | rfl
    | by_cases hx : x ∈ (H : Set X) <;> simp [hx, LocallyConstant.indicator]
  obtain ⟨c, hc⟩ := huniq _ h1SB (by
      intro s hs Y
      have : (Y + s ∈ (H : Set X) ↔ Y ∈ (H : Set X)) := H.add_mem_cancel_right (hSH hs)
      by_cases hY : Y ∈ (H : Set X)
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (this.mpr hY)]; rfl
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (this.mp h))]) (by
      intro Y hY
      refine Set.indicator_of_notMem (fun hYH => hY ?_) _
      have hB0 : Y₀ ∈ B := by
        by_contra h; exact hY₀ (hsupp _ h)
      have hB1 : Y₀ + Y ∈ B := by
        by_contra h; exact hY₀ ((hH Y hYH).symm.trans (hsupp _ h))
      exact hB _ _ hB0 hB1)
  have e0 := congrFun hc 0
  rw [Set.indicator_of_mem (show (0 : X) ∈ (H : Set X) from H.zero_mem)] at e0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at e0
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at e0
  refine ⟨c⁻¹, ?_, hHo, hHk⟩
  funext y
  have ey := congrFun hc y
  simp only [Pi.smul_apply, smul_eq_mul] at ey ⊢
  rw [ey, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.SBClosure

theorem GlobalTheory.SBClosure.main : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  intro F _ _ v m k S B hB f hf hf0 hinv hsupp huniq
  haveI : NonarchimedeanAddGroup (Fin k → Fv F v) := GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin k => Fv F v)
  haveI : NonarchimedeanAddGroup (Matrix (Fin m) (Fin k) (Fv F v)) :=
    GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin m => Fin k → Fv F v)
  exact GlobalTheory.SBClosure.eq_smul_indicator_closure S B hB f hf hf0 hinv hsupp huniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatricesInvariantSupportedEqSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  first | exact @GlobalTheory.SBClosure.main | exact GlobalTheory.SBClosure.main | (intros; apply GlobalTheory.SBClosure.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVacuumEqSmulIndicatorSplitPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

theorem vacuum_eq_smul_indicator : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ φ₀ h0 hne hfix huniq
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linearModel_intertwiner_goodSplitPlace Bs Γ X om om' hTr
  have hfSB : ι φ₀ ∈ GlobalTheory.WeilM.SB _ := hι.bij.mapsTo h0
  have hf0 : ι φ₀ ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn h0 (zero_mem _) ?_
    rw [h, map_zero]
  have hinv : ∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, ι φ₀ (Y + s) = ι φ₀ Y := by
    rintro _ ⟨u, hu, hu0, rfl⟩ Y
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hA := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inl hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hA
    exact (hι.trans u hat hu0 φ₀ h0 φ₀ h0 hA Y).symm
  have hsupp : ∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, ι φ₀ Y = 0 := by
    intro Y hY
    simp only [GlobalTheory.VacShape.Bd, Set.mem_setOf_eq, not_forall] at hY
    obtain ⟨x, hx, hx0, rfl, u, hu, hu0, hne1⟩ := hY
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hB := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inr hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hB
    have hm := hι.mult u hat hu0 φ₀ h0 φ₀ h0 hB x hx hx0
    by_contra h
    exact hne1 ((mul_eq_right₀ h).mp hm.symm)
  obtain ⟨c, hc, hop, hcp⟩ := GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul Bs.v₁ _ _ (GlobalTheory.T.latticePairingTrivialMatrices_sub_mem Bs Γ X om om' hTr L₁ L₂) (ι φ₀) hfSB hf0 hinv hsupp
    (GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq)
  obtain ⟨P, Λ, hPΛ⟩ := GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices Bs Γ X om om' hTr L₁ L₂ hop hcp
  refine ⟨ι, P, Λ, c, hι, fun Y => ?_⟩
  have hY := congrFun hc Y
  rw [Pi.smul_apply, smul_eq_mul] at hY
  rw [hY]
  congr 1
  by_cases h : Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set _)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show P.val * Y ∈ (matLat (Fin a') Λ : Set _) from (hPΛ Y).1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show P.val * Y ∉ (matLat (Fin a') Λ : Set _) from fun h' => h ((hPΛ Y).2 h'))]

end GlobalTheory.VacShape

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVacuumEqSmulIndicatorSplitPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.latticeVacuum_eq_smul_indicator_splitPlace : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  first | exact @GlobalTheory.VacShape.vacuum_eq_smul_indicator | exact GlobalTheory.VacShape.vacuum_eq_smul_indicator | (intros; apply GlobalTheory.VacShape.vacuum_eq_smul_indicator <;> assumption)
end
end
