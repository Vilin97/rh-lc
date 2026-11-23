module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesK
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypesW
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypes
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TypeBOfMemTypSp
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
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
import Mathlib.RingTheory.PicardGroup
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.MultOperatorShiftsTwist
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TypeBOfMemTypSp
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.FiniteDimensionalTypeSpaceOfDisc

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_sep {α : Type} (X : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ X] :
    ∃ S : Finset α, ∀ w ∈ X, (∀ a ∈ S, w a = 0) → w = 0 := by
  classical
  let Ker : Finset α → Submodule ℂ (α → ℂ) := fun S =>
    X ⊓ ⨅ a ∈ S, LinearMap.ker (LinearMap.proj a : (α → ℂ) →ₗ[ℂ] ℂ)
  have hmem : ∀ S w, w ∈ Ker S ↔ w ∈ X ∧ ∀ a ∈ S, w a = 0 := by
    intro S w
    simp only [Ker, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  have hfd : ∀ S, FiniteDimensional ℂ (Ker S) := fun S => Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ d, ∃ S, Module.finrank ℂ (Ker S) = d := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS0⟩ := Nat.find_spec hex
  have hS : ∀ S', Module.finrank ℂ (Ker S) ≤ Module.finrank ℂ (Ker S') := fun S' => by
    rw [hS0]
    exact Nat.find_min' hex ⟨S', rfl⟩
  refine ⟨S, fun w hw h0 => ?_⟩
  by_contra hne
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have hlt : Ker (insert a S) < Ker S := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun he => ?_)
    · rw [hmem] at hv ⊢
      exact ⟨hv.1, fun b hb => hv.2 b (Finset.mem_insert_of_mem hb)⟩
    · have hwS : w ∈ Ker S := (hmem S w).2 ⟨hw, h0⟩
      rw [← he, hmem] at hwS
      exact ha (hwS.2 a (Finset.mem_insert_self a S))
  have := hfd S
  exact absurd (hS (insert a S)) (not_le.2 (Submodule.finrank_lt_finrank_of_lt hlt))

theorem typSp_tw_le {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} (hK : K' ≤ detKer n)
    (W' : Submodule ℂ (Kinf E n → ℂ)) (U : Submodule ℂ (Sm E n)) (z : ℂ) :
    TypSp K' W' (tw U z) ≤ (TypSp K' W' U).map (mulChi n (Model.absC E z)).toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨hφ, hT⟩
  obtain ⟨χ, hχ, rfl⟩ := hφ
  refine ⟨χ, Submodule.subset_span ⟨hχ, ?_⟩, rfl⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) :=
    (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK (-z)

theorem finiteDimensional_type_space_of_disc (hA : AdmDisc) {N : ℕ} (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [hW : FiniteDimensional ℂ W] :
    ∀ {n : ℕ} (t : Tr E n), n ≤ N → t.Disc → FiniteDimensional ℂ (TypSp (Kf N K n) (Wf N W n) t.space) := by
  intro n t
  induction t with
  | leaf V z =>
    intro _ ht
    show FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) (tw V z))
    rcases ht with ⟨rfl, -, -⟩ | ⟨-, hV⟩
    · have : Subsingleton (GA E 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩
      infer_instance
    · have : FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) V) :=
        hA E _ _ _ (isOpen_Kf hK _) (fd_Wf hW _) V hV
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) (Wf N W _) V z)
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro hN ht
    obtain ⟨ht₁, ht₂⟩ := ht
    have : FiniteDimensional ℂ (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2))) := by
      have := ih₁ (by omega) ht₁
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    have : FiniteDimensional ℂ (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) := by
      have := ih₂ (by omega) ht₂
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    set Y := tens2 (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2)))
      (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) with hY
    have : FiniteDimensional ℂ Y := fd_tens2 _ _
    set X := TypSp (Kf N K (r + s)) (Wf N W (r + s)) (Tr.node t₁ t₂).space with hX
    have : FiniteDimensional ℂ (Wf N W (r + s)) := fd_Wf hW _
    obtain ⟨S, hS⟩ := exists_sep (Wf N W (r + s))
    set T := Tset r s (Kf N K (r + s)) with hTdef
    have hI : ∀ φ ∈ X, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ := by
      intro φ hφ
      have hf : φ ∈ (Tr.node t₁ t₂).space := typSp_le _ _ _ hφ
      rw [Tr.space] at hf
      apply memInd2_of_span
      apply Submodule.span_mono _ hf
      intro φ h
      exact h.1
    have key : ∀ φ ∈ X, ∀ t ∈ T, ∀ k : Kinf E (r + s),
        (fun m : GA E r × GA E s =>
          φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t))) ∈ Y := by
      intro φ hφ t ht k
      have hT := typeB_of_mem_typSp hφ
      refine tens_typ ((hI φ hφ).2 k t) (fun y => ⟨fun u hu x₁ => ?_, fun x₁ => ?_⟩)
        (fun x => ⟨fun u hu x₂ => ?_, fun x₂ => ?_⟩)
      · have h1 : lev (Ad E) r s (x₁ * finGL E r u, y) =
            lev (Ad E) r s (x₁, y) * finGL E (r + s) (lev (Af E) r s (u, 1)) := by
          rw [← Slice1.lev_finGL, map_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (u, 1))
        have e : lev (Ad E) r s (x₁ * finGL E r u, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x₁, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (u, 1) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (u, 1))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_left hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x₁, y) * finGL E (r + s) t)
        have hW₁ := Wf_left (W := W) hN hw k
        convert hW₁ using 1
        funext k₁
        show φ.1 _ = _
        rw [infGL_comm, ← mul_assoc, Slice1.lev_infGL_right]
        simp only [map_mul, Slice1.toUnits_levK]
      · have h1 : lev (Ad E) r s (x, x₂ * finGL E s u) =
            lev (Ad E) r s (x, x₂) * finGL E (r + s) (lev (Af E) r s (1, u)) := by
          rw [← Slice2.lev_finGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (1, u))
        have e : lev (Ad E) r s (x, x₂ * finGL E s u) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (1, u))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_right hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x, x₂) * finGL E (r + s) t)
        have hW₂ := Wf_right (W := W) hN hw k
        convert hW₂ using 1
        funext k₂
        show φ.1 _ = _
        have h1 : lev (Ad E) r s (x, x₂ * infGL E s (Unitary.toUnits k₂)) =
            lev (Ad E) r s (x, x₂) * infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂)) := by
          rw [← Slice2.lev_infGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        rw [h1]
        simp only [map_mul, Slice2.toUnits_levK]
        rw [infGL_comm (Unitary.toUnits k) t]
        simp only [← mul_assoc]
        rw [mul_assoc (lev (Ad E) r s (x, x₂)) (infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂))),
          infGL_comm (lev (Cinf E) r s (1, Unitary.toUnits k₂)) t, ← mul_assoc]
    have inj : ∀ φ ∈ X, (∀ t ∈ T, ∀ k ∈ S, ∀ m : GA E r × GA E s,
        φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) = 0) → φ = 0 := by
      intro φ hφ h0
      have hT := typeB_of_mem_typSp hφ
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨x, m, t, k, l, ht, hl, hg⟩ := Tset_spec (isOpen_Kf hK (r + s)) g
      have hw := hT.2 (lev (Ad E) r s m * finGL E (r + s) t)
      have hz := hS _ hw (fun κ hκ => by
        show φ.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0
        rw [mul_assoc, ← infGL_comm]
        exact h0 t ht κ hκ m)
      have e : g = unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) *
          finGL E (r + s) l := by
        rw [hg]
        simp only [mul_assoc]
      show φ.1 g = 0
      rw [e, hT.1 l hl, (hI φ hφ).1]
      exact congrFun hz k
    let f : X →ₗ[ℂ] (↥T × ↥S → Y) :=
      { toFun := fun φ p => ⟨fun m => φ.1.1 (lev (Ad E) r s m *
            (infGL E (r + s) (Unitary.toUnits p.2.1) * finGL E (r + s) p.1.1)),
          key φ.1 φ.2 p.1.1 p.1.2 p.2.1⟩
        map_add' := fun φ ψ => funext fun p => Subtype.ext (funext fun m => rfl)
        map_smul' := fun c φ => funext fun p => Subtype.ext (funext fun m => rfl) }
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have h0 := inj φ.1 φ.2 fun t ht k hk m => by
      have := congrArg (fun F => (F (⟨t, ht⟩, ⟨k, hk⟩)).1 m) hφ
      exact this
    exact Subtype.ext h0

theorem fd_typSp (hA : AdmDisc) {N : ℕ} (t : Tr E N) (ht : t.Disc) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (TypSp K W t.space) := by
  have := finiteDimensional_type_space_of_disc hA K hK W t le_rfl ht
  refine Submodule.finiteDimensional_of_le (S₂ := TypSp (Kf N K N) (Wf N W N) t.space) (Submodule.span_le.2 ?_)
  rintro φ ⟨hφ, hT⟩
  exact Submodule.subset_span ⟨hφ, fun u hu g => hT.1 u (Kf_top hu) g, fun g => lt_le_Wf (typeB_lt hT g)⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.MulMemPairSpace

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem heckeAct_smul {a b : ℕ} {ι : Type} [Fintype ι] (h : HeckeM E a b ι) (c : ℂ) (f : ι → H E a b → ℂ) :
    heckeAct h (c • f) = c • heckeAct h f := by
  funext i x
  simp only [heckeAct, Pi.smul_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => ?_
  ring

theorem tendsto_heckeAct {a b : ℕ} {ι : Type} [Fintype ι] (h : HeckeM E a b ι) {F : ℕ → ι → H E a b → ℂ}
    {F₀ : ι → H E a b → ℂ} (hF : ∀ i x, Tendsto (fun k => F k i x) atTop (𝓝 (F₀ i x))) (i : ι) (x : H E a b) :
    Tendsto (fun k => heckeAct h (F k) i x) atTop (𝓝 (heckeAct h F₀ i x)) := by
  simp only [heckeAct, Finsupp.sum]
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun g _ => (hF j _).const_mul _

theorem fd_prodSpan {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W₁]
    [FiniteDimensional ℂ W₂] :
    FiniteDimensional ℂ (Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) := by
  let B : W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] (X × Y → ℂ) :=
    LinearMap.mk₂ ℂ (fun w₁ w₂ k => (w₁ : X → ℂ) k.1 * (w₂ : Y → ℂ) k.2)
      (fun _ _ _ => by funext k; simp [add_mul]) (fun _ _ _ => by funext k; simp [mul_assoc])
      (fun _ _ _ => by funext k; simp [mul_add]) (fun _ _ _ => by funext k; simp [mul_left_comm])
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift B)) (Submodule.span_le.2 ?_)
  rintro _ ⟨w₁, h₁, w₂, h₂, rfl⟩
  exact ⟨TensorProduct.tmul ℂ (⟨w₁, h₁⟩ : W₁) (⟨w₂, h₂⟩ : W₂), by simp [B]⟩

theorem mul_mem_pairSpace {a b : ℕ} {U₁ U₁' : Submodule ℂ (Sm E a)} {U₂ U₂' : Submodule ℂ (Sm E b)}
    (M₁ : GA E a → ℂ) (M₂ : GA E b → ℂ) (h₁ : ∀ φ ∈ U₁, ∃ ψ ∈ U₁', ψ.1 = fun x => M₁ x * φ.1 x)
    (h₂ : ∀ φ ∈ U₂, ∃ ψ ∈ U₂', ψ.1 = fun x => M₂ x * φ.1 x) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) :
    (fun x => (M₁ x.1 * M₂ x.2) * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩ := hF
    obtain ⟨ψ₁, hψ₁, e₁⟩ := h₁ φ₁ hφ₁
    obtain ⟨ψ₂, hψ₂, e₂⟩ := h₂ φ₂ hφ₂
    refine Submodule.subset_span ⟨ψ₁, hψ₁, ψ₂, hψ₂, ?_⟩
    funext x
    rw [e₁, e₂]
    ring
  | zero =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (0 : H E a b → ℂ) x) = 0 := by funext x; simp
    rw [e]
    exact Submodule.zero_mem _
  | add F G _ _ hF hG =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (F + G) x) =
        (fun x => (M₁ x.1 * M₂ x.2) * F x) + fun x => (M₁ x.1 * M₂ x.2) * G x := by
      funext x; simp [mul_add]
    rw [e]
    exact Submodule.add_mem _ hF hG
  | smul c F _ hF =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (c • F) x) = c • fun x => (M₁ x.1 * M₂ x.2) * F x := by
      funext x; simp [mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ c hF

theorem cf_one_left (n : ℕ) (c : GL (Fin n) (Af E)) : InducedTensorMap.cf n 1 c = finGL E n c := by
  simp [InducedTensorMap.cf]

theorem cf_one_right (n : ℕ) (k : Kinf E n) : InducedTensorMap.cf n k 1 = infGL E n (Unitary.toUnits k) := by
  simp [InducedTensorMap.cf]

theorem limVec : LimVec := by
  intro hA E _ _ _ a b ι _ t₁ t₂ s₁ s₂ K₁ K₂ W₁ W₂ C lam lam₀ f hK₁ hK₂ hW₁ hW₂ _hC hs₁ hs₂ ht₁ ht₂ hst₁ hst₂
    hz₁ hz₂ hf0 hfP hfT hEig hLam
  classical

  have et₁ : ∀ k, t₁ k = s₁.strip.addTw fun i => (t₁ k).twists.getD i 0 := fun k =>
    (eq_addTw (t₁ k)).trans (by rw [hst₁ k])
  have et₂ : ∀ k, t₂ k = s₂.strip.addTw fun i => (t₂ k).twists.getD i 0 := fun k =>
    (eq_addTw (t₂ k)).trans (by rw [hst₂ k])
  have es₁ : s₁ = s₁.strip.addTw fun i => s₁.twists.getD i 0 := eq_addTw s₁
  have es₂ : s₂ = s₂.strip.addTw fun i => s₂.twists.getD i 0 := eq_addTw s₂
  have hd₁ : s₁.Disc := disc_of_good s₁ hs₁
  have hd₂ : s₂.Disc := disc_of_good s₂ hs₂
  have hb₁ : s₁.strip.AllLeaves fun _ V => _root_.GlobalTheory.CuspRep.IsStable V := (allLeaves_strip s₁ _).2 (allLeaves_stable_of_disc s₁ hd₁)
  have hb₂ : s₂.strip.AllLeaves fun _ V => _root_.GlobalTheory.CuspRep.IsStable V := (allLeaves_strip s₂ _).2 (allLeaves_stable_of_disc s₂ hd₂)

  let γ₁ : ℕ → ℕ → ℂ := fun k i => s₁.twists.getD i 0 - (t₁ k).twists.getD i 0
  let γ₂ : ℕ → ℕ → ℂ := fun k i => s₂.twists.getD i 0 - (t₂ k).twists.getD i 0
  have hγ₁ : ∀ i, Tendsto (fun k => γ₁ k i) atTop (𝓝 0) := fun i => by
    have := (tendsto_const_nhds (x := s₁.twists.getD i 0)).sub (hz₁ i)
    rwa [sub_self] at this
  have hγ₂ : ∀ i, Tendsto (fun k => γ₂ k i) atTop (𝓝 0) := fun i => by
    have := (tendsto_const_nhds (x := s₂.twists.getD i 0)).sub (hz₂ i)
    rwa [sub_self] at this
  let Φ : ℕ → H E a b → ℂ := fun k x => mult s₁.strip (γ₁ k) x.1 * mult s₂.strip (γ₂ k) x.2
  have hΦne : ∀ k x, Φ k x ≠ 0 := fun k x => mul_ne_zero (mult_ne _ _ _) (mult_ne _ _ _)
  have hΦlim : ∀ x, Tendsto (fun k => Φ k x) atTop (𝓝 1) := fun x => by
    have := (mult_tendsto s₁.strip γ₁ hγ₁ x.1).mul (mult_tendsto s₂.strip γ₂ hγ₂ x.2)
    rwa [one_mul] at this

  let K₁' : Subgroup (GL (Fin a) (Af E)) := K₁ ⊓ Cint E a
  let K₂' : Subgroup (GL (Fin b) (Af E)) := K₂ ⊓ Cint E b
  have hK₁' : IsOpen (K₁' : Set (GL (Fin a) (Af E))) :=
    hK₁.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hK₂' : IsOpen (K₂' : Set (GL (Fin b) (Af E))) :=
    hK₂.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E b)
  haveI := hW₁
  haveI := hW₂
  haveI : FiniteDimensional ℂ (TypSp K₁' W₁ s₁.space) := fd_typSp hA s₁ hd₁ K₁' hK₁' W₁
  haveI : FiniteDimensional ℂ (TypSp K₂' W₂ s₂.space) := fd_typSp hA s₂ hd₂ K₂' hK₂' W₂
  let X₀ : Submodule ℂ (H E a b → ℂ) := pairSpace (TypSp K₁' W₁ s₁.space) (TypSp K₂' W₂ s₂.space)
  haveI : FiniteDimensional ℂ X₀ := fd_tens2 _ _

  have hmul₁ : ∀ k, ∀ φ ∈ (t₁ k).space, ∃ ψ ∈ s₁.space, ψ.1 = fun x => mult s₁.strip (γ₁ k) x * φ.1 x := by
    intro k φ hφ
    rw [et₁ k] at hφ
    obtain ⟨ψ, hψ, e⟩ := flat s₁.strip hb₁ _ (fun i => s₁.twists.getD i 0) φ hφ
    exact ⟨ψ, by rw [es₁]; exact hψ, e⟩
  have hmul₂ : ∀ k, ∀ φ ∈ (t₂ k).space, ∃ ψ ∈ s₂.space, ψ.1 = fun x => mult s₂.strip (γ₂ k) x * φ.1 x := by
    intro k φ hφ
    rw [et₂ k] at hφ
    obtain ⟨ψ, hψ, e⟩ := flat s₂.strip hb₂ _ (fun i => s₂.twists.getD i 0) φ hφ
    exact ⟨ψ, by rw [es₂]; exact hψ, e⟩
  have hg : ∀ k i, (fun x => Φ k x * f k i x) ∈ X₀ := by
    intro k i
    refine pair_typ (mul_mem_pairSpace _ _ (hmul₁ k) (hmul₂ k) (hfP k i)) ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩
    · have e₁ : x.1 * finGL E a u₁ = x.1 * InducedTensorMap.cf a 1 u₁ := by rw [cf_one_left]
      have e₂ : x.2 * finGL E b u₂ = x.2 * InducedTensorMap.cf b 1 u₂ := by rw [cf_one_left]
      show mult s₁.strip (γ₁ k) (x.1 * finGL E a u₁) * mult s₂.strip (γ₂ k) (x.2 * finGL E b u₂) *
          f k i (x * (finGL E a u₁, finGL E b u₂)) = Φ k x * f k i x
      rw [e₁, e₂, mult_rinv _ _ _ _ hu₁.2, mult_rinv _ _ _ _ hu₂.2, (hfT k i).1 u₁ hu₁.1 u₂ hu₂.1 x]
    · have e : (fun kk : Kinf E a × Kinf E b =>
          Φ k (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))) *
            f k i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2)))) =
          Φ k x • fun kk : Kinf E a × Kinf E b =>
            f k i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))) := by
        funext kk
        have e₁ : x.1 * infGL E a (Unitary.toUnits kk.1) = x.1 * InducedTensorMap.cf a kk.1 1 := by rw [cf_one_right]
        have e₂ : x.2 * infGL E b (Unitary.toUnits kk.2) = x.2 * InducedTensorMap.cf b kk.2 1 := by rw [cf_one_right]
        show mult s₁.strip (γ₁ k) (x.1 * infGL E a (Unitary.toUnits kk.1)) *
            mult s₂.strip (γ₂ k) (x.2 * infGL E b (Unitary.toUnits kk.2)) * _ = _
        rw [e₁, e₂, mult_rinv _ _ _ _ (one_mem _), mult_rinv _ _ _ _ (one_mem _)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ ((hfT k i).2 x)

  let V := ι → X₀
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  let gk : ℕ → V := fun k i => ⟨fun x => Φ k x * f k i x, hg k i⟩
  have hgk0 : ∀ k, gk k ≠ 0 := by
    intro k h0
    apply hf0 k
    funext i x
    have := congrArg (fun v : V => ((v i : X₀) : H E a b → ℂ) x) h0
    simp only [gk] at this
    exact (mul_eq_zero.1 this).resolve_left (hΦne k x)
  let c : ℕ → ℂ := fun k => ((‖e (gk k)‖⁻¹ : ℝ) : ℂ)
  let v : ℕ → (Fin (Module.finrank ℂ V) → ℂ) := fun k => c k • e (gk k)
  have hv : ∀ k, v k ∈ Metric.sphere (0 : Fin (Module.finrank ℂ V) → ℂ) 1 := by
    intro k
    have hne : e (gk k) ≠ 0 := (LinearEquiv.map_ne_zero_iff e).2 (hgk0 k)
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ V) → ℂ) 1).tendsto_subseq hv
  let u : V := e.symm w
  have hu0 : u ≠ 0 := by
    intro h0
    have : w = 0 := by simpa [u] using congrArg e h0
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at hw
    exact zero_ne_one hw
  let F : ι → H E a b → ℂ := fun i x => ((u i : X₀) : H E a b → ℂ) x

  have hA' : ∀ i x, Tendsto (fun k => c (φ k) * (Φ (φ k) x * f (φ k) i x)) atTop (𝓝 (F i x)) := by
    intro i x
    let L : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] ℂ :=
      (LinearMap.proj x) ∘ₗ X₀.subtype ∘ₗ (LinearMap.proj i) ∘ₗ e.symm.toLinearMap
    have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
    have h1 := (hL.tendsto w).comp hlim
    refine h1.congr fun k => ?_
    show L (v (φ k)) = _
    show ((e.symm (c (φ k) • e (gk (φ k)))) i : H E a b → ℂ) x = _
    rw [map_smul, LinearEquiv.symm_apply_apply]
    rfl
  have hconv : ∀ i x, Tendsto (fun k => c (φ k) * f (φ k) i x) atTop (𝓝 (F i x)) := by
    intro i x
    have h1 := (hA' i x).div ((hΦlim x).comp hφ.tendsto_atTop) one_ne_zero
    rw [div_one] at h1
    refine h1.congr fun k => ?_
    show c (φ k) * (Φ (φ k) x * f (φ k) i x) / Φ (φ k) x = _
    rw [mul_left_comm, mul_div_cancel_left₀ _ (hΦne _ x)]
  refine ⟨F, ?_, fun i => ?_, fun i => ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩, fun h hh => ?_⟩
  · intro hF0
    apply hu0
    funext i
    exact Subtype.ext (funext fun x => congrFun (congrFun hF0 i) x)
  · exact tensor_span_mono (typSp_le _ _ _) (typSp_le _ _ _) (u i).2
  · refine tendsto_nhds_unique ((hconv i _).congr fun k => ?_) (hconv i x)
    rw [(hfT (φ k) i).1 u₁ hu₁ u₂ hu₂ x]
  · let Z : Submodule ℂ (Kinf E a × Kinf E b → ℂ) :=
      Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
    haveI : FiniteDimensional ℂ Z := fd_prodSpan W₁ W₂
    refine (Submodule.closed_of_finiteDimensional Z).mem_of_tendsto
      (tendsto_pi_nhds.2 fun kk => hconv i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))))
      (Eventually.of_forall fun k => ?_)
    exact Z.smul_mem (c (φ k)) ((hfT (φ k) i).2 x)
  · funext i x
    have h1 := tendsto_heckeAct h hconv i x
    have h2 : ∀ k, heckeAct h (fun i x => c (φ k) * f (φ k) i x) i x = lam (φ k) h * (c (φ k) * f (φ k) i x) := by
      intro k
      rw [show (fun i x => c (φ k) * f (φ k) i x) = c (φ k) • f (φ k) from rfl, heckeAct_smul, hEig (φ k) h hh]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have h3 := ((hLam h hh).comp hφ.tendsto_atTop).mul (hconv i x)
    have := tendsto_nhds_unique (h1.congr h2) h3
    simpa only [Pi.smul_apply, smul_eq_mul] using this

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end
end
