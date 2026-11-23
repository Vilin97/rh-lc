module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.AdUnitBLie
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.CbStrictMonoOfAnti
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.ExistsFrameOfPositiveVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.SmoothVec
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.TopLevelPointwiseIdentity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.Vanish
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.SpecAbstract

section

@[expose] public section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SpecAux

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X : Type*}

theorem spec_sum_mem {β : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp)))
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (f : β → X → (Wq →L[ℂ] Wp)) (s : Finset β) (hf : ∀ i ∈ s, f i ∈ 𝓕) :
    (fun x => ∑ i ∈ s, f i x) ∈ 𝓕 := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x => ∑ i ∈ (∅ : Finset β), f i x) = fun _ => (0 : Wq →L[ℂ] Wp) := by
      funext x; simp
    rw [e]; exact h0
  · intro a s ha ih hf
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e]
    exact hadd _ (hf a (Finset.mem_insert_self a s)) _
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem spec_iter {ι : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (S : X → ι → Submodule ℂ Wq)
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) (n : ℕ) :
    ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J ∈ 𝓕) ∧
      ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ,
        ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) g v = (lam σ Y₀) ^ n • J g v := by
  induction n with
  | zero => exact ⟨hJ, fun g _ σ v _ => by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact hA _ h1
    · intro g hg σ v hv
      rw [Function.iterate_succ_apply']
      simp only [ContinuousLinearMap.smul_apply]
      rw [heig _ h1 g hg σ v hv Y₀, h2 g hg σ v hv]
      simp only [smul_smul]
      congr 1
      have hcg := hc g hg
      rw [pow_succ]
      field_simp

end SpecAux

theorem spec_abstract {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (hsmul : ∀ F ∈ 𝓕, ∀ c : ℂ, (fun x => c • F x) ∈ 𝓕)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (hinj : Function.Injective (fun σ => lam σ Y₀))
    (S : X → ι → Submodule ℂ Wq) (hS : ∀ g ∈ G, DirectSum.IsInternal (S g))
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) :
    ∃ dec : ι → X → (Wq →L[ℂ] Wp), (∀ σ, dec σ ∈ 𝓕) ∧ (∀ g ∈ G, J g = ∑ σ, dec σ g) ∧
      (∀ σ Y, ∀ g ∈ G, T Y (dec σ) g = (c g * lam σ Y) • dec σ g) ∧
      ∀ g ∈ G, ∀ σ v, ∃ w ∈ S g σ, dec σ g v = J g w := by
  classical
  have hinjOn : Set.InjOn (fun σ => lam σ Y₀) (Finset.univ : Finset ι) := fun a _ b _ h => hinj h
  have hit := spec_iter 𝓕 G T c hc Y₀ hA lam S heig J hJ
  obtain ⟨dec, hdec⟩ : ∃ dec : ι → X → (Wq →L[ℂ] Wp), ∀ σ x, dec σ x =
      ∑ n ∈ Finset.range ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x := ⟨_, fun _ _ => rfl⟩
  have hmem : ∀ σ, dec σ ∈ 𝓕 := by
    intro σ
    have hfun : dec σ = fun x => ∑ n ∈ Finset.range
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (fun n x => (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x) n x := funext (hdec σ)
    rw [hfun]
    exact spec_sum_mem 𝓕 h0 hadd _ _ fun n _ => hsmul _ (hit n).1 _
  have hkey : ∀ σ, ∀ g ∈ G, ∀ τ, ∀ v ∈ S g τ, dec σ g v = if σ = τ then J g v else 0 := by
    intro σ g hg τ v hv
    have h1 : dec σ g v =
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).eval (lam τ Y₀)) • J g v := by
      rw [hdec, Polynomial.eval_eq_sum_range, Finset.sum_smul, _root_.sum_apply]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [_root_.smul_apply, (hit n).2 g hg τ v hv, smul_smul]
    rw [h1]
    split_ifs with hστ
    · subst hστ
      have he := Lagrange.eval_basis_self hinjOn (Finset.mem_univ σ)
      rw [he, one_smul]
    · have he := Lagrange.eval_basis_of_ne (v := fun σ => lam σ Y₀) hστ (Finset.mem_univ τ)
      rw [he, zero_smul]
  have htop : ∀ g ∈ G, ∀ v : Wq, v ∈ ⨆ i, S g i := fun g hg v => by
    rw [(hS g hg).submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine ⟨dec, hmem, ?_, ?_, ?_⟩
  · intro g hg
    ext v
    rw [_root_.sum_apply]
    refine Submodule.iSup_induction (S g) (motive := fun v => J g v = ∑ σ, dec σ g v)
      (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      simp only [hkey _ g hg τ w hw, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp
    · intro x y hx hy
      simp only [map_add (f := _), hx, hy, Finset.sum_add_distrib]
  · intro σ Y g hg
    ext v
    rw [_root_.smul_apply]
    refine Submodule.iSup_induction (S g)
      (motive := fun v => T Y (dec σ) g v = (c g * lam σ Y) • dec σ g v) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      rw [heig (dec σ) (hmem σ) g hg τ w hw Y, hkey σ g hg τ w hw]
      split_ifs with hστ
      · rw [hστ]
      · rw [smul_zero, smul_zero]
    · simp
    · intro x y hx hy
      rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  · intro g hg σ v
    refine Submodule.iSup_induction (S g)
      (motive := fun v => ∃ w ∈ S g σ, dec σ g v = J g w) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      by_cases hστ : σ = τ
      · subst hστ
        exact ⟨w, hw, by rw [hkey σ g hg σ w hw, if_pos rfl]⟩
      · exact ⟨0, zero_mem _, by rw [hkey σ g hg τ w hw, if_neg hστ, map_zero]⟩
    · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
    · rintro x y ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add (f := _), map_add (f := _), h₁, h₂]⟩

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts

section

@[expose] public section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_sub {k r m : ℕ} {vs vs' : List (Fin (2 * r + k + 1) → ℂ)} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r vs Bs) (hs : ∀ v ∈ vs', v ∈ vs) : IsFrameOf k r vs' Bs :=
  ⟨h.1, h.2.1, fun a v hv => h.2.2 a v (hs v hv)⟩

theorem radial_decomposition_of_parts' : RadialDecompositionOfParts := by
  intro _hC2 _hCC hCap hRTA hBr hTP
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D hPl hD hGGD J hJ
  obtain ⟨hP, hz, hz', hTz, hTz', hπ, hπ'⟩ := hPl
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
  have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
  obtain ⟨Y₀, hY₀⟩ := exists_sep hP
  obtain ⟨f, hfi, hfx, hfr⟩ := comb_match hP
  have hloc : ∀ g : Mx P.k P.r, ∃ (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
      (e : Fin (2 * P.r + P.k + 1) → ℂ) (S : M.Ty (Pp P) → Submodule ℂ Wq),
      g ∈ Glev P.k P.r (Fin.last P.r) ∩ D →
      IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs ∧ inWb P.k P.r e ∧ herm (Hpk P.k P.r) e z = 0 ∧
      herm (Hpk P.k P.r) e e = 1 ∧ IsFrameOf P.k P.r [z, e] (fun a => g *ᵥ Bs a) ∧ DirectSum.IsInternal S ∧
      ∀ σ, ∀ v ∈ S σ, ∀ w : ℂ, capRep P.k P.r π' Bs w v = M.xC (Pp P) σ (w - ((P.k : ℂ) - 2) / 2) • v := by
    intro g
    by_cases hg : g ∈ Glev P.k P.r (Fin.last P.r) ∩ D
    · obtain ⟨Bs, e', e, hB1, he', he'z, he'e, hB2, he, hez, hee, hB3⟩ :=
        geom_package hz hz' hT hT' hg.1 (hGGD g hg.2)
      obtain ⟨S, hSi, -, hSe⟩ := hBr Wq (Pp P) (Pp_OK hP) rfl z' e' π' hz' hT' hπ' he' he'z he'e
      exact ⟨Bs, e, S, fun _ => ⟨hB1, he, hez, hee, hB3, hSi, fun σ v hv w => hSe Bs hB2 σ w v hv⟩⟩
    · exact ⟨fun _ _ => 0, 0, fun _ => ⊥, fun h => absurd h hg⟩
  choose Bs e S hBS using hloc
  obtain ⟨dec, hdecF, hsum, heigd, hcomp⟩ := spec_abstract (FFl P.k P.r z z' π π' (Fin.last P.r) D)
    (Glev P.k P.r (Fin.last P.r) ∩ D) ff_zero (fun F₁ h₁ F₂ h₂ => ff_add h₁ h₂) (fun F h c => ff_smul h c)
    (fun Y F => tL P.k P.r z z' (Fin.last P.r) Y 1 1 F) (fun x => (GGl P.k P.r z z' x : ℂ))
    (fun g hg => by exact_mod_cast hGGD g hg.2) Y₀
    (fun F hF => ff_GGinv hz hz' hD hGGD (hTP Wp Wq P.k P.r z z' π π' (Fin.last P.r) D Y₀ 1 1 hz hz' hD F hF))
    (fun σ Y => M.xC (Pp P) σ Y) hY₀ S (fun g hg => (hBS g hg).2.2.2.2.2.1)
    (by
      intro F hF g hg σ v hv Y
      have hc : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := by ring
      rw [top_level_pointwise_identity hCap hRTA hz hz' hD hπ'.2.1 hπ'.2.2.1 hF hg (hGGD g hg.2) (Bs g) (hBS g hg).1 Y v,
        (hBS g hg).2.2.2.2.2.2 σ v hv _, hc, ContinuousLinearMap.map_smul, smul_smul])
    J hJ
  have hvan : ∀ σ, σ ∉ Set.range f → ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ D, dec σ g = 0 := by
    intro σ hσ g hg
    ext v
    obtain ⟨w, hw, hdw⟩ := hcomp g hg σ v
    rw [hdw, _root_.zero_apply]
    by_contra hne
    obtain ⟨hB1, he, hez, hee, hB3, -, hSe⟩ := hBS g hg
    have hsm := J_smoothVec hz hz' hD hπ'.2.1.1 hJ hg w
    have hlin : ∀ W : ℂ, IsLinearMap ℂ (capRep P.k P.r π (fun a => g *ᵥ Bs g a) W) := fun W =>
      capRep_linear hπ hne hsm (fun a => g *ᵥ Bs g a) (frame_sub hB3 (by simp)) W
    have hμ : ∀ W : ℂ, capRep P.k P.r π (fun a => g *ᵥ Bs g a) W (J g w) =
        M.xC (Pp P) σ (W - ((P.k : ℂ) - 2) / 2) • J g w := by
      intro W
      rw [← left_ad hz hz' hD hπ'.2.1.1 hJ hg (Bs g) (frame_sub hB1 (by simp)) W w,
        hRTA Wp Wq P.k P.r (P.k - 1) z z' π π' D hz hz' hD hπ'.2.1 hπ'.2.2.1 J hJ g hg (Bs g)
          (frame_sub hB1 (by simp)) W w,
        hSe σ w hw W, ContinuousLinearMap.map_smul]
    obtain ⟨ρ, hρ⟩ := vanish_match hBr hP hz hT hπ he hez hee _ hB3 hlin hne _ hμ
    exact hσ (hfr σ ρ hρ)
  refine ⟨fun ρ => dec (f ρ), fun ρ => hdecF (f ρ), ?_, ?_⟩
  · intro g hg
    have h1 : ∑ σ ∈ Finset.univ.image f, dec σ g = ∑ σ, dec σ g :=
      Finset.sum_subset (Finset.subset_univ _) (fun σ _ hσ => hvan σ
        (fun ⟨ρ, hρ⟩ => hσ (hρ ▸ Finset.mem_image_of_mem f (Finset.mem_univ ρ))) g hg)
    rw [hsum g hg, ← h1, Finset.sum_image (fun a _ b _ h => hfi h)]
  · intro ρ Y g hg
    have h := heigd (f ρ) Y g hg
    rw [h, hfx ρ Y]

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end
end
