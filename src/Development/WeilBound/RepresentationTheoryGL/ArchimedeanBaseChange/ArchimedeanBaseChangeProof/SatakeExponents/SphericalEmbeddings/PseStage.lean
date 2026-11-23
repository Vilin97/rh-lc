module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageB

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem kinj_prod₂MapR (π₁ : Representation ℂ (GL (Fin r) k) U) {π₂ : Representation ℂ (GL (Fin t) k) X}
    {π₂' : Representation ℂ (GL (Fin t) k) Y} (f : π₂.IntertwiningMap π₂') (hf : KInj k f) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.lTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f F).1.1 x =
        TensorProduct.map LinearMap.id f.toLinearMap (F.1.1 x) := rfl
    rw [LinearMap.lTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)), π₂ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin t)), π₂ h x = ((1 : ↥(KO k (Fin t)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)),
      LinearMap.lTensor U (π₂ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (1, h) with hℓ
    have hℓK : ∀ b, ℓ b ∈ KO k (Two (Fin r) (Fin t) b) := by
      intro b
      cases b
      · exact one_mem _
      · exact hh
    have hEmb : leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ ∈ KO k (Fin (r + t)) := by
      have hfacts := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (r + t))
        (Two (Fin r) (Fin t)) (two (stdSum (rfl : r + t = r + t)))).1 ℓ 1 (one_mem _)
      simpa using hfacts.mpr ⟨hℓK, one_mem _⟩
    have hDelta : deltaHalf k (Two (Fin r) (Fin t)) ℓ = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one (fun a _ => ?_)
      
      apply isUnram_absPow k _ _
      obtain ⟨g, hg⟩ := hℓK a
      rw [← hg]
      have heq : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact heq.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (hEmb) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (1, h) = LinearMap.lTensor U (π₂ h) := by
      apply TensorProduct.ext'
      intro u x
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, hDelta,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_lTensor π₂ (KO k (Fin t) : Set (GL (Fin t) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

theorem kinj_prod₂MapL {π₁ : Representation ℂ (GL (Fin r) k) X} {π₁' : Representation ℂ (GL (Fin r) k) Y}
    (f : π₁.IntertwiningMap π₁') (hf : KInj k f) (π₂ : Representation ℂ (GL (Fin t) k) U) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.rTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂ F).1.1 x =
        TensorProduct.map f.toLinearMap LinearMap.id (F.1.1 x) := rfl
    rw [LinearMap.rTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)), π₁ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin r)), π₁ h x = ((1 : ↥(KO k (Fin r)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)),
      LinearMap.rTensor U (π₁ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (h, 1) with hℓ
    have hℓK : ∀ b, ℓ b ∈ KO k (Two (Fin r) (Fin t) b) := by
      intro b
      cases b
      · exact hh
      · exact one_mem _
    have hEmb : leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ ∈ KO k (Fin (r + t)) := by
      have hfacts := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (r + t))
        (Two (Fin r) (Fin t)) (two (stdSum (rfl : r + t = r + t)))).1 ℓ 1 (one_mem _)
      simpa using hfacts.mpr ⟨hℓK, one_mem _⟩
    have hDelta : deltaHalf k (Two (Fin r) (Fin t)) ℓ = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one (fun a _ => ?_)
      
      apply isUnram_absPow k _ _
      obtain ⟨g, hg⟩ := hℓK a
      rw [← hg]
      have heq : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact heq.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (hEmb) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (h, 1) = LinearMap.rTensor U (π₁ h) := by
      apply TensorProduct.ext'
      intro x u
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, hDelta,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_rTensor π₁ (KO k (Fin r) : Set (GL (Fin r) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

end PositivityTheory.Rg.BcB.N3.PseStage

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageC

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_append {r t : ℕ} (a : Fin r → ℂˣ) (b : Fin t → ℂˣ) :
    (fun i => unrChar k (Fin.append a b i)) = Fin.append (fun i => unrChar k (a i)) (fun i => unrChar k (b i)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp


theorem prin_append {r t : ℕ} (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((prod₂ (prinSeries ψ₁) (prinSeries ψ₂)).Equiv (prinSeries (Fin.append ψ₁ ψ₂))) := by
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (k := k) ψ₁ ψ₂
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (k := k) ψ₁ ψ₂
  exact ⟨E1.trans E2⟩


theorem iP_append (r t : ℕ) (A : Fin r → ℂˣ) (B : Fin t → ℂˣ) :
    Nonempty ((prod₂ (iP (k := k) A) (iP (k := k) B)).Equiv (iP (k := k) (Fin.append A B))) := by
  have key : ∀ χ : Fin (r + t) → kˣ →* ℂˣ,
      χ = Fin.append (fun i => unrChar k (A i)) (fun i => unrChar k (B i)) →
      Nonempty ((prod₂ (prinSeries fun i => unrChar k (A i))
        (prinSeries fun i => unrChar k (B i))).Equiv (prinSeries χ)) := by
    rintro χ rfl
    exact prin_append _ _
  exact key _ (unrChar_append A B)

theorem mainGen {r t : ℕ} {VA VB Vc Vc' Vi Vi' Vo Vo' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB]
    [Module ℂ VB] [AddCommGroup Vc] [Module ℂ Vc] [AddCommGroup Vc'] [Module ℂ Vc'] [AddCommGroup Vi] [Module ℂ Vi]
    [AddCommGroup Vi'] [Module ℂ Vi'] [AddCommGroup Vo] [Module ℂ Vo] [AddCommGroup Vo'] [Module ℂ Vo']
    (πA : Representation ℂ (GL (Fin r) k) VA) (πB : Representation ℂ (GL (Fin t) k) VB)
    {πc : Representation ℂ (GL (Fin 2) k) Vc} {πc' : Representation ℂ (GL (Fin 2) k) Vc'}
    {πi : Representation ℂ (GL (Fin (2 + t)) k) Vi} {πi' : Representation ℂ (GL (Fin (2 + t)) k) Vi'}
    {πo : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo} {πo' : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo'}
    (Ei : (prod₂ πc πB).Equiv πi) (Ei' : (prod₂ πc' πB).Equiv πi') (Eo : (prod₂ πA πi).Equiv πo)
    (Eo' : (prod₂ πA πi').Equiv πo') (T : πc.IntertwiningMap πc') (hT : KInj k T) :
    ∃ T' : πo.IntertwiningMap πo', KInj k T' := by
  let M : πi.IntertwiningMap πi' :=
    Ei'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapL T πB).comp Ei.symm.toIntertwiningMap)
  have hM : KInj k M :=
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapL T hT _)) (kinj_equiv _)
  exact ⟨Eo'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapR πA M).comp Eo.symm.toIntertwiningMap),
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapR _ M hM)) (kinj_equiv _)⟩

end PositivityTheory.Rg.BcB.N3.PseStage

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStage

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem main {r t : ℕ} (A : Fin r → ℂˣ) (a b : ℂˣ) (B : Fin t → ℂˣ)
    (T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a])) (hT : KInj k T) :
    ∃ T' : (iP (k := k) (Fin.append A (Fin.append ![a, b] B))).IntertwiningMap
      (iP (k := k) (Fin.append A (Fin.append ![b, a] B))), KInj k T' := by
  obtain ⟨Ei⟩ := iP_append (k := k) 2 t ![a, b] B
  obtain ⟨Ei'⟩ := iP_append (k := k) 2 t ![b, a] B
  obtain ⟨Eo⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![a, b] B)
  obtain ⟨Eo'⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![b, a] B)
  exact mainGen _ _ Ei Ei' Eo Eo' T hT


variable (k) in
theorem stageLift : StageLift k := by
  intro n η i j hij ⟨T, hT⟩
  obtain ⟨r, hr⟩ : ∃ r, i.val = r := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, n = r + (2 + t) := ⟨n - (r + 2), by have := j.isLt; omega⟩
  subst ht
  obtain ⟨A, hA⟩ : ∃ A : Fin r → ℂˣ, ∀ l, A l = η (Fin.castAdd (2 + t) l) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin t → ℂˣ, ∀ l, B l = η (Fin.natAdd r (Fin.natAdd 2 l)) := ⟨_, fun _ => rfl⟩
  have ei : ∀ h : 0 < 2, Fin.natAdd r (Fin.castAdd t (⟨0, h⟩ : Fin 2)) = i := fun h => Fin.ext (by simp [hr])
  have ej : ∀ h : 1 < 2, Fin.natAdd r (Fin.castAdd t (⟨1, h⟩ : Fin 2)) = j := fun h => Fin.ext (by simp [hr, hij])
  have h1 : η = Fin.append A (Fin.append ![η i, η j] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · rw [Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [ei h]; rfl
        | ⟨1, h⟩ => rw [ej h]; rfl
      · rw [Fin.append_right, hB]
  have h2 : η ∘ Equiv.swap i j = Fin.append A (Fin.append ![η j, η i] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · have e1 : Fin.castAdd (2 + t) l ≠ i := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have e2 : Fin.castAdd (2 + t) l ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2, Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [Function.comp_apply, ei h, Equiv.swap_apply_left]; rfl
        | ⟨1, h⟩ => rw [Function.comp_apply, ej h, Equiv.swap_apply_right]; rfl
      · have e1 : Fin.natAdd r (Fin.natAdd 2 m) ≠ i := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        have e2 : Fin.natAdd r (Fin.natAdd 2 m) ≠ j := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        rw [Fin.append_right, hB, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2]
  have := main (k := k) A (η i) (η j) B T hT
  rw [← h1, ← h2] at this
  exact this

end PositivityTheory.Rg.BcB.N3.PseStage

end
end
end
