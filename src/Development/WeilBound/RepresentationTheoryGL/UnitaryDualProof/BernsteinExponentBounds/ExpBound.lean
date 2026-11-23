module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterTheta.HasCentralCharCompThetaW
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterZero.AsmCentralZero
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvTransposeInvTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.FirstPairExistence.ExistsPairFirst
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.BesselSum
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCell

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ContragredientSwap.IsIrreducibleOfContraSwap

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped TensorProduct
open GlobalTheory.CompanionTheory.BZSegComm
open Zc.Cos (invT)

namespace PositivityTheory.RgUd.Exp.Comm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isIrreducible_comp_invT {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)) := by
  have e : (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)).comp (invT : GL (Fin N) k →* GL (Fin N) k) = π :=
    MonoidHom.ext fun g => congrArg (⇑π) (invT_invT g)
  exact GlobalTheory.SwapTwo.isIrreducible_of_comp (invT : GL (Fin N) k →* GL (Fin N) k) (by rw [e]; exact h)

theorem isIrreducible_of_contra_swap {r t N : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hAa : IsAdmissible A) (hAi : A.IsIrreducible) (hBa : IsAdmissible B) (hBi : B.IsIrreducible)
    (h : r + t = N) (h' : t + r = N)
    (ρX : Representation ℂ (GL (Fin N) k) X) (ρY : Representation ℂ (GL (Fin N) k) Y)
    (eX : ρX.Equiv (ind₂ (stdSum h) (extTensor A B)))
    (eY : (ind₂ (stdSum h') (extTensor (contra B) (contra A))).Equiv ρY)
    (hX : ρX.IsIrreducible) : ρY.IsIrreducible := by
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap A B
  obtain ⟨ga⟩ := nonempty_comp_invT_equiv_contra A hAa hAi
  obtain ⟨gb⟩ := nonempty_comp_invT_equiv_contra B hBa hBi
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv
    (((compEquiv eX _).trans κ.symm).trans ((ind₂Equiv _ (τ.trans (extTensorCongr gb ga))).trans eY))
    (isIrreducible_comp_invT _ hX)

theorem prodIrr_swap_isIrreducible (F G : Fin 2 → IrrGL (k := k)) (e₀ : G 0 = F 1) (e₁ : G 1 = F 0) {N : ℕ}
    (hd : ∑ a, (F a).1 = N) (hd' : ∑ a, (G a).1 = N) (hX : (prodIrr F hd).IsIrreducible) :
    (prodIrr G hd').IsIrreducible := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have h : (F 0).1 + (F 1).1 = N := (Fin.sum_univ_two _).symm.trans hd
  have h' : (G 0).1 + (G 1).1 = N := (Fin.sum_univ_two _).symm.trans hd'
  have h'' : (F 1).1 + (F 0).1 = N := by rw [← e₀, ← e₁]; exact h'
  have aX := hA k N _ _ (isSmooth_prodIrr _ hd) hX
  have a0 := hA k _ _ (F 0).rep (F 0).2.rep.smooth (F 0).2.rep.irr
  have a1 := hA k _ _ (F 1).rep (F 1).2.rep.smooth (F 1).2.rep.irr
  have R0 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 0).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a0 a0
  have R1 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 1).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a1 a1
  have RX := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin N) k) (GlobalTheory.LocalThetaGL.compact_open_basis _)
    _ _ _ _ aX aX
  have c0i := R0.1 (F 0).2.rep.irr
  have c1i := R1.1 (F 1).2.rep.irr
  have c0a := hA k _ _ (contra (F 0).rep) (isSmooth_contra _) c0i
  have c1a := hA k _ _ (contra (F 1).rep) (isSmooth_contra _) c1i
  obtain ⟨ε⟩ := nonempty_ind₂_contra_equiv hA F hd h
  have e0 := R0.2.1.some
  have e1 := R1.2.1.some
  obtain ⟨m⟩ := nonempty_ind₂_equiv_multiProd (k := k) (d := fun a => (G a).1) hd' h' fun a => (G a).rep
  have E₃ : ∀ (u v : IrrGL (k := k)), u = F 1 → v = F 0 → ∀ h₁ : u.1 + v.1 = N,
      Nonempty ((ind₂ (stdSum h'') (extTensor (F 1).rep (F 0).rep)).Equiv
        (ind₂ (stdSum h₁) (extTensor u.rep v.rep))) := by
    rintro _ _ rfl rfl _
    exact ⟨.refl _⟩
  have e₄ := (E₃ _ _ e₀ e₁ h').some
  exact isIrreducible_of_contra_swap (contra (F 0).rep) (contra (F 1).rep) c0a c0i c1a c1i h h''
    (contra (prodIrr F hd)) (prodIrr G hd') ε.symm
    (((ind₂Equiv _ (extTensorCongr e1.symm e0.symm)).trans e₄).trans m) (RX.1 hX)

end Lemmas

theorem comm2Irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.Comm2Irr k := by
  intro x y N hd hd' hX
  exact prodIrr_swap_isIrreducible ![x, y] ![y, x] rfl rfl hd hd' hX

end PositivityTheory.RgUd.Exp.Comm

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.IrreducibleFactors.FactorIrr

section

@[expose] public section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.RgUd.Exp.Fact

theorem factorIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.FactorIrr k := by
  intro r t V W _ _ _ _ A B hAs hBs hI
  classical
  obtain ⟨hX, hIirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hI
  let ρ' := (extTensor A B).comp (GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hAs hBs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have key : ∀ R : Submodule ℂ (V ⊗[ℂ] W), (∀ l, ∀ y ∈ R, ρ' l y ∈ R) → R = ⊥ ∨ R = ⊤ := by
    intro R hR
    let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
      { carrier := {f | ∀ g, f.1.1 g ∈ R}
        add_mem' := fun ha hb g => add_mem (ha g) (hb g)
        zero_mem' := fun g => zero_mem R
        smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
    have hYs : ∀ g, ∀ f ∈ Y, prod₂ A B g f ∈ Y := fun g f hf x => hf (x * g)
    rcases hIirr Y hYs with hY | hY
    · left
      refine (Submodule.eq_bot_iff R).2 fun u hu => ?_
      obtain ⟨f, h1, h2⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := fun g => by
        rcases h2 g with h | ⟨l, c, h⟩
        · rw [h]; exact zero_mem R
        · rw [h]; exact R.smul_mem c (hR l u hu)
      rw [hY, Submodule.mem_bot] at hf
      rw [← h1, hf]; rfl
    · right
      refine eq_top_iff.2 fun u _ => ?_
      obtain ⟨f, h1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
      have hf : f ∈ Y := by rw [hY]; exact Submodule.mem_top
      rw [← h1]; exact hf 1
  have h0 : ¬ ∀ z : V ⊗[ℂ] W, z = 0 := by
    intro h
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h _).trans (h _).symm)))
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact h0 fun z => TensorProduct.induction_on (motive := fun z => z = 0) z rfl
      (fun x w => by rw [Subsingleton.elim x 0, TensorProduct.zero_tmul])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    exact h0 fun z => TensorProduct.induction_on (motive := fun z => z = 0) z rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
  refine ⟨(GlobalTheory.CuspRep.isIrreducible_iff A).2 ⟨hV, fun S hS => ?_⟩,
    (GlobalTheory.CuspRep.isIrreducible_iff B).2 ⟨hW, fun S hS => ?_⟩⟩
  · obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℂ W, ψ w₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw₀ ((Module.forall_dual_apply_eq_zero_iff ℂ w₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V ψ
    have hL : ∀ x w, L (x ⊗ₜ w) = ψ w • x := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.rTensor W S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x, hS _ _ x.2⟩ ⊗ₜ
          B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.rTensor_tmul, hL]; exact S.smul_mem _ x.2
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : s ⊗ₜ[ℂ] w₀ ∈ R := ⟨⟨s, hs⟩ ⊗ₜ w₀, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (s ⊗ₜ w₀) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hψ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : v ⊗ₜ[ℂ] w₀ ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hψ).1 h2
  · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
    let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
    have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
    let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
    have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
      rintro l _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
        exact ⟨A ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
          ⟨B ((GlobalTheory.SmGL.leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    have hLR : ∀ y ∈ R, L y ∈ S := by
      rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    rcases key R hR with h | h
    · left
      refine (Submodule.eq_bot_iff S).2 fun s hs => ?_
      have hm : x₀ ⊗ₜ[ℂ] s ∈ R := ⟨x₀ ⊗ₜ ⟨s, hs⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      have : L (x₀ ⊗ₜ s) = 0 := by rw [hm, map_zero]
      rw [hL] at this
      exact (smul_eq_zero.1 this).resolve_left hφ
    · right
      refine eq_top_iff.2 fun v _ => ?_
      have hm : x₀ ⊗ₜ[ℂ] v ∈ R := by rw [h]; exact Submodule.mem_top
      have h2 := hLR _ hm
      rw [hL] at h2
      exact (S.smul_mem_iff hφ).1 h2

end PositivityTheory.RgUd.Exp.Fact
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ThetaProducts.ThetaProd

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.ThetaPf

open GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.ThetaW

theorem thetaProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.ThetaProd k := by
  intro r t V W _ _ _ _ A B _ _
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum (rfl : r + t = r + t)) (stdSum (add_comm t r))
    (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap (k := k) A B
  exact ⟨(compInvTEquiv (prod₂ A B)).symm.trans (κ.symm.trans
    (ind₂Equiv _ (τ.trans (extTensorCongr (compInvTEquiv B) (compInvTEquiv A)))))⟩

end PositivityTheory.RgUd.Exp.ThetaPf

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ExpBoundOf

section

@[expose] public section

namespace PositivityTheory.RgUd.Exp.Final

open PositivityTheory.RgUd.Exp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem expBound (hL : ExpLow k) : ExpBound k :=
  PositivityTheory.RgUd.Exp.expBound_of k
    (Move2.moveLast k (Fact.factorIrr k) (Comm.comm2Irr k)) (Move2.moveFirst k (Fact.factorIrr k) (Comm.comm2Irr k))
    (ThetaPf.thetaProd k) (thetaFacts k) (centralProd2 k) hL

theorem expBound_of : ExpLow k → ExpBound k := expBound k

end PositivityTheory.RgUd.Exp.Final
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound

section

@[expose] public section

namespace PositivityTheory.RgUd

theorem expBound (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : ExpBound k :=
  Exp.Final.expBound_of k (Cell.expLow k (Form.Final.besselSum k) (Cell.openCell k))

end PositivityTheory.RgUd
end
end
