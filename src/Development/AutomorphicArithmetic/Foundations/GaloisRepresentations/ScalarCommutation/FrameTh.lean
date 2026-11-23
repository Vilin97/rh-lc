module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemFn
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHasEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPPart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PhiEx

section

@[expose] public section

theorem UpperTheory.Gal.Spc.phiEx :
    UpperTheory.Gal.Spc.PhiEx :=
  UpperTheory.Gal.W2.Seed.phiEx_holds
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP

section

@[expose] public section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pExtP :
    ExtP := by
  intro Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2
  let F : X × X₂ → V := fun p =>
    if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0
  have key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ →
      F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g)) := by
    intro γ g g₂ hγ
    have h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂ := ⟨γ, hγ⟩
    dsimp only [F]
    rw [dite_eq_left h]
    have hδ := h.choose_spec
    generalize h.choose = δ at hδ ⊢
    have hε : (ι (δ⁻¹ * γ)).2 ∈ K₂ := by
      have e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹ := by
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
        group
      rw [e]
      exact K₂.mul_mem hδ (K₂.inv_mem hγ)
    have e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
      group
    rw [← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0 := by
    intro g g₂ h
    dsimp only [F]
    rw [dite_eq_right h]
  have mem : F ∈ forms ι (K.prod K₂) ξ := by
    refine ⟨fun γ p => ?_, fun k hk p => ?_⟩
    · obtain ⟨g, g₂⟩ := p
      have e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂ := by
          simpa [map_mul, mul_assoc] using hδ
        rw [key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]
        congr 2
        simp [mul_assoc]
      · rw [zero g g₂ h, map_zero]
        apply zero
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨γ⁻¹ * δ, ?_⟩
        simpa [map_mul, mul_assoc] using hδ
    · obtain ⟨g, g₂⟩ := p
      obtain ⟨k1, k2⟩ := k
      rw [Subgroup.mem_prod] at hk
      have hk1 : k1 ∈ K := hk.1
      have hk2 : k2 ∈ K₂ := hk.2
      have e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂ := by
          rw [← mul_assoc]
          exact K₂.mul_mem hδ hk2
        rw [key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]
      · rw [zero g g₂ h, zero]
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ, ?_⟩
        have := K₂.mul_mem hδ (K₂.inv_mem hk2)
        simpa [mul_assoc] using this
  refine ⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩
  · show F (g, 1) = φ g
    rw [key 1 g 1 (by simp)]
    simp
  · by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
    · obtain ⟨δ, hδ⟩ := h
      exact Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩
    · exact Or.inl fun g => zero g g₂ h
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FrameTh

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw Gam0 rat sim mat th th0 invT_val mem_lev comp_th sim_th th_rat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open GlobalTheory.LFun (KGL)
open Formalism.UG (Hecke conv hAct)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem frame_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]
    {S : Setup A n p} (F : Frame S) (g : GUf E n) : F.th g = th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem th_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} (hn : 0 < n) (w₀ : Plc E) (S₀ : Finset (Plc E))
    (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (hS : ∀ u ∈ S₀, (p : 𝓞 E) ∉ u.asIdeal) (k : GUf E n)
    (h1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) (h2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) :
    th k ∈ lev S₀ Kw := by
  have hall : ∀ w : Plc E, comp w k ∈ KGL w (n := n) := fun w => by
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · exact h2 w hw
    · rw [h1 w hw]; exact one_mem _
  have hsim : sim k ∈ CertificateRingHomMap.ZU := ((pIntConj E n k w₀ hn).2.1 hall)
  refine mem_lev.2 ⟨by rw [sim_th]; exact inv_mem hsim, fun w hw => ?_, fun w _ _ => ?_⟩
  · rw [comp_th, h1 w (hS w hw)]
    have : GlobalTheory.CuspRep.invT n _ (1 : GLw n w) = 1 := map_one _
    rw [this]; exact one_mem _
  · rw [comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hall w)

theorem eigEx : EigEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  refine ⟨(GlobalTheory.CuspRep.invT n E).prodMap invMonoidHom, fun y => ⟨rfl, rfl⟩, fun J g θ hg => ?_⟩
  obtain ⟨φ, hφ0, hφT, hφj, hφe⟩ := phiEx E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  have hkey : ∀ h, V.Φ (th (F.tr.sec h)) = φ h := fun h => by
    have := hφj (F.tr.sec h) fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _
    rw [frame_th, F.j_tr, F.tr.j_sec] at this
    exact this.symm
  have hfun : (fun h => V.Φ (th (F.tr.sec h))) = φ := funext hkey
  have hCen : Ty.Cen 1 := ⟨fun g => by simp, map_one _⟩
  refine pHasEigOf (pStdForm pMuStar) pPInt (pPPart pJEq) pExtP E A n p S F.tr _ ((CertificateRingHomMap.xi V.W V.jz).comp _) (fun g => V.Φ (th g))
    (fun γ g => ?_) (fun k h1 h2 g => ?_) ?_ Ty.K₀ Ty.cms (fun k hk h => ?_) J (fun j => (g j).fn) θ (Ty.tf 1)
    (fun j => (memFn E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy (g j) (θ j) (hg j)).1)
    (pTfAdm _ _ Ty 1 (map_one _)).1.1 ?_ (fun j => ?_)
  · show V.Φ (th (rat γ * g)) = _
    rw [map_mul, th_rat, V.form.left]
    rfl
  · have hpos : Odd n → 0 < n := Odd.pos
    have hk := th_mem (hpos hn) w₀ V.S V.Kw hOff.1 k h1 h2
    have hw₀ : (p : 𝓞 E) ∉ w₀.asIdeal := hOff.1 _ V.shape.mem
    have hc : comp w₀ (th k) = 1 := by
      rw [comp_th, h1 w₀ hw₀]; exact map_one _
    have hJ : comp w₀ (th k) ∈ V.J := by rw [hc]; exact one_mem _
    show V.Φ (th (g * k)) = V.Φ (th g)
    have hr' := V.form.right (th k) hk hJ (th g)
    have hone : V.χ ⟨comp w₀ (th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (th k), hJ⟩ : V.J) = 1 := Subtype.ext hc
      rw [this, map_one]
    rw [map_mul, hr', hone]
    simp
  · obtain ⟨h, hh⟩ := Function.ne_iff.1 hφ0
    exact ⟨F.tr.sec h, by rw [hkey]; exact hh, fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _⟩
  · rw [hkey, hkey, hφT k (Ty.le hk) h, Ty.ker k hk]
    simp
  · rw [hfun]
    funext a
    have := pTfCen pAvgK pTfAdm _ _ Ty 1 hCen _ φ hφT a
    simpa using this
  · rw [hfun]
    exact hφe (g j) (θ j) (hg j)

end UpperTheory.Gal.Spc
end
end
end
