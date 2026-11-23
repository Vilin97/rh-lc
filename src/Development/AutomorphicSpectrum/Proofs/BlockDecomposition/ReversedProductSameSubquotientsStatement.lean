module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContraIsSubquotient

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraSq

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := fun s => by
  have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact hρ s

theorem exists_smooth_extension {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (l₀ : Module.Dual ℂ S.toSubmodule) (hl₀ : ∀ h ∈ K, ∀ s, l₀ (S.toRepresentation h s) = l₀ s) :
    ∃ l : smoothPart ρ.dual, (∀ h ∈ K, contra ρ h l = l) ∧
      ∀ s : S.toSubmodule, (l : Module.Dual ℂ V) s = l₀ s := by
  have hmem : ∀ x : fixed S.toRepresentation K,
      (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K := by
    intro x
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    exact congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)
  let ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K := LinearMap.codRestrict _ _ hmem
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ((x : S.toSubmodule) : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc
    ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)
  refine ⟨l, hl1, fun s => ?_⟩
  have key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀ := by
    refine GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_
    · have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V))
        (hl1 h⁻¹ (inv_mem hh))
      simp only [contra_apply, inv_inv] at h1
      exact h1
    · have h2 := hl2 (ι ⟨w, hw⟩)
      have h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hr ⟨w, hw⟩
      simp only [LinearMap.comp_apply, h3] at h2
      exact h2
  exact LinearMap.congr_fun key s

def annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap τ) : Subrepresentation (contra ρ) :=
  ⟨{ carrier := {l | ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0}
     add_mem' := fun {a b} ha hb s hs => by simp [ha s hs, hb s hs]
     zero_mem' := fun s _ => by simp
     smul_mem' := fun c a ha s hs => by simp [ha s hs] }, by
    intro h l hl s hs
    have h0 : f (S.toRepresentation h⁻¹ s) = 0 := by
      rw [f.isIntertwining, hs, map_zero]
    exact hl _ h0⟩

theorem mem_annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {l : smoothPart ρ.dual} :
    l ∈ (annih S f).toSubmodule ↔ ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0 :=
  Iff.rfl

def pull {ρ : Representation ℂ G V} (S : Subrepresentation ρ) (g : W →ₗ[ℂ] S.toSubmodule) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ W :=
  (S.toSubmodule.subtype ∘ₗ g).dualMap

theorem pull_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {g : W →ₗ[ℂ] S.toSubmodule}
    (hg : ∀ w, f (g w) = w) {l : smoothPart ρ.dual} (hl : l ∈ (annih S f).toSubmodule)
    (s : S.toSubmodule) : pull S g (l : Module.Dual ℂ V) (f s) = (l : Module.Dual ℂ V) s := by
  have h0 : f (g (f s) - s) = 0 := by
    have : f (g (f s) - s) = f (g (f s)) - f s := map_sub f.toLinearMap _ _
    rw [this, hg, sub_self]
  have h1 := mem_annih.1 hl _ h0
  have h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0 := h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2

def restrLin {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toSubmodule →ₗ[ℂ] smoothPart τ.dual where
  toFun l := ⟨pull S g ((l : smoothPart ρ.dual) : Module.Dual ℂ V),
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_contra ρ (l : smoothPart ρ.dual)).mem_nhds (by simp)) fun h hh => by
        have hh' : contra ρ h (l : smoothPart ρ.dual) = l := hh
        refine LinearMap.ext fun w => ?_
        obtain ⟨s, rfl⟩ := hf w
        show pull S g _ (τ h⁻¹ (f s)) = pull S g _ (f s)
        rw [← f.isIntertwining, pull_apply_map hg l.2, pull_apply_map hg l.2]
        have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (s : V)) hh'
        simp only [contra_apply] at h1
        exact h1)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

theorem restrLin_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (l : (annih S f).toSubmodule) (s : S.toSubmodule) :
    (restrLin hf hg l : Module.Dual ℂ W) (f s) = ((l : smoothPart ρ.dual) : Module.Dual ℂ V) s :=
  pull_apply_map hg l.2 s

theorem restrLin_comm {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (h : G) (l : (annih S f).toSubmodule) (w : W) :
    (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) w =
      (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ w) := by
  have e : ∀ s : S.toSubmodule,
      (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) =
        (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s)) := fun s => by
    rw [← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]
    rfl
  have := e (g w)
  rwa [hg w] at this

def restr {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toRepresentation.IntertwiningMap (contra τ) where
  toLinearMap := restrLin hf hg
  isIntertwining' h :=
    LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun w => restrLin_comm hf hg h l w)

theorem contra_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  intro G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.toLinearMap
    (LinearMap.range_eq_top.2 hf)
  have hg' : ∀ w, f (g w) = w := fun w => LinearMap.congr_fun hg w
  refine ⟨annih S f, restr hf hg', fun m => ?_⟩
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra τ m).mem_nhds (by simp))
  have hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) =
      (m : Module.Dual ℂ W) (f s) := by
    intro h hh s
    have h1 : contra τ h⁻¹ m = m := hKs (inv_mem hh)
    have h2 := congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1
    simp only [contra_apply, inv_inv] at h2
    rw [f.isIntertwining]
    exact h2
  obtain ⟨l, -, hl⟩ := exists_smooth_extension hρ S ho hc
    ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix
  have hmem : l ∈ (annih S f).toSubmodule := fun s hs => by
    have h1 := hl s
    have h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s) := rfl
    rw [h1, h2, hs, map_zero]
  refine ⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩
  obtain ⟨s, rfl⟩ := hf w
  show pull S g (l : Module.Dual ℂ V) (f s) = _
  rw [pull_apply_map hg' hmem]
  exact hl s

end GlobalTheory.CompanionTheory.ContraSq

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotientAltBis

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isSubquotient_contra_of_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W), IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | exact GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

theorem contra_contra_of_equiv {G V W U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} {υ : Representation ℂ G U}
    (E₁ : (contra σ).Equiv τ) (E₂ : (contra τ).Equiv υ) (E₃ : υ.Equiv σ) :
    Nonempty ((contra (contra σ)).Equiv σ) :=
  ⟨((GlobalTheory.ContraRefl.contraEquiv E₁).symm.trans E₂).trans E₃⟩

theorem prodIrr_equiv_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : y = x)
    (hy : ∑ a, (y a).1 = N) (hx : ∑ a, (x a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr x hx)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem contra_contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  intro k _ _ _ _ hA h N x hd
  refine Exists.elim (contra_prodIrr hA x hd) fun hd₁ H₁ => H₁.elim fun E₁ => ?_
  refine Exists.elim (contra_prodIrr hA (fun a => Zc.dualCl (x a)) hd₁) fun hd₂ H₂ => H₂.elim fun E₂ => ?_
  refine (prodIrr_equiv_of_eq (funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA (x a)) hd₂ hd).elim fun E₃ => ?_
  exact contra_contra_of_equiv E₁ E₂ E₃

end GlobalTheory.CompanionTheory.ContraProd

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProductStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.double_contragredient_of_induced_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenRev

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h



theorem isSubquotient_prodIrr_rev : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type}
      [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible →
      IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  intro k _ _ _ _ hA hGK h N x hd hd' W _ _ σ _ hi hsq

  obtain ⟨hdy, ⟨E1⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => x (Fin.rev a)) hd'

  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (fun a => Zc.dualCl (x (Fin.rev a))) hdy
  have ex : (fun a => Zc.dualCl ((fun a => Zc.dualCl (x (Fin.rev a))) (Fin.rev a))) = x := funext fun a => by
    simp only [Fin.rev_rev]
    exact GlobalTheory.T.dual_class_involutive hA (x a)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LSocle.prodIrr_congr ex hd2 hd
  have h1 : IsSubquotient σ ((prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy).comp (Zc.Cos.thetaW k N)) :=
    isSubquotient_of_equiv hsq (E2.trans E3).symm
  have h2 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy) := by
    have := GlobalTheory.CompanionTheory.WordProd.RowCell.isSubquotient_pullback (Zc.Cos.thetaW k N) h1
    rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at this
  have hs : IsSmooth (σ.comp (Zc.Cos.thetaW k N)) := h2.isSmooth (isSmooth_prodIrr _ _)
  have hi' : Representation.IsIrreducible (σ.comp (Zc.Cos.thetaW k N)) :=
    GlobalTheory.CosocleComp.isIrreducible_comp (GlobalTheory.CompanionTheory.LSocle.thetaW_surjective N) hi
  have h3 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (contra (prodIrr (fun a => x (Fin.rev a)) hd')) :=
    isSubquotient_of_equiv h2 E1.symm
  have h4 := GlobalTheory.T.isSubquotient_contra_of_isSubquotient (GlobalTheory.SqIntUnit.compactOpen_basis k N) _ _ (isSmooth_contra _) h3
  obtain ⟨E4⟩ := GlobalTheory.T.double_contragredient_of_induced_product hA (fun a => x (Fin.rev a)) hd'
  obtain ⟨E5⟩ := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK σ hs hi'
  exact isSubquotient_of_equiv_left E5.symm (isSubquotient_of_equiv h4 E4)

end GlobalTheory.CompanionTheory.GenRev
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotientsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.reversed_product_same_subquotients : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | exact GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | (intros; apply GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev <;> assumption)
end
end
