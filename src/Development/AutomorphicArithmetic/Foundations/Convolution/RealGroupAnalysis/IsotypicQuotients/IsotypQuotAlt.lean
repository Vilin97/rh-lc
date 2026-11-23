module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Isotyp

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotyp :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Isotyp F := by
  intro F _ _ _ π v σ h x
  have h1 : (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1) = ⊤ := by
    have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
        π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
      refine Subtype.ext ?_
      change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g)) y.1 =
        (TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, TR.infGL_comm]
    have fin_loc {k : GL (Fin 2) (Af F)}
        (hk : GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k = 1)
        (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
        π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
      simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]
    let W : Submodule ℂ π.V := ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1
    have hact : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W := by
      intro g x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep v g) _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g u, f.2 g u⟩
    have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W := by
      intro T hT x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g u => by
        rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨u, rfl⟩
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := hact (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k) _ (hcomm
          (π.finPart ((GlobalTheory.CuspRep.locGL F 2 v (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k))⁻¹ * k))
          (fin_loc (GlobalTheory.CuspRep.LocEx.map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact hcomm _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact hcomm _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (GlobalTheory.CuspRep.locGL F 2 v g)) y.1)) x hx
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨y, hy, rfl⟩
      exact ⟨_, hop o y hy, rfl⟩) with hb | ht
    · have e : W = ⊥ := hi (hb.trans (Submodule.map_bot _).symm)
      obtain ⟨f, h0, hf⟩ := h
      exact False.elim (h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩)))
    · exact hi (ht.trans (Submodule.map_subtype_top _).symm)
  refine (show (⊤ : Submodule ℂ π.V) ≤ _ from h1 ▸ iSup_le fun f => ?_) Submodule.mem_top
  exact fun y hy => Submodule.subset_span ⟨f.1, f.2, hy⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuotAlt

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

private theorem irr_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (h.eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ)).imp
    (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotypQuot :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.IsotypQuot F := by
  intro F _ _ _ π v σ σ' h X _ _ ρ i hi hρ hs
  let T : Set (σ.V →ₗ[ℂ] X) := {j | ∀ g u, j (σ.ρ g u) = ρ g (j u)}
  let R : Submodule ℂ X := ⨆ j ∈ T, LinearMap.range j
  have hR : ∀ u, i u ∈ R := fun u => by
    refine Submodule.span_le.2 ?_ (hs u)
    rintro _ ⟨p, hp, x, rfl⟩
    refine (Submodule.span_le (p := R.comap p)).2 ?_ (isotyp F π v σ h x)
    rintro _ ⟨j, hj, z, rfl⟩
    exact Submodule.mem_iSup_of_mem (p ∘ₗ j) (Submodule.mem_iSup_of_mem (fun g u => by
      simp only [LinearMap.comp_apply, hj, hp]) ⟨z, rfl⟩)
  have irr := irr_sub σ.ρ σ.irred
  have irr' := irr_sub σ'.ρ σ'.irred
  obtain ⟨u₀, hu₀⟩ : ∃ u, i u ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hi (LinearMap.ext hn)
  obtain ⟨M, hM⟩ : ∃ M, Maximal (fun N : Submodule ℂ X => (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N) M := by
    refine (zorn_le_nonempty₀ {N : Submodule ℂ X | (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N}
      (fun c hc hch y hy => ⟨sSup c, ⟨fun g x hx => ?_, fun hx => ?_⟩,
      fun z hz => le_sSup hz⟩) ⊥ ⟨fun g x hx => by simp_all, by simpa using hu₀⟩).imp fun M hM => hM.2
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact le_sSup hN ((hc hN).1 g x h1)
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact (hc hN).2 h1
  obtain ⟨j, hj, hjM⟩ : ∃ j ∈ T, ¬ LinearMap.range j ≤ M := by
    by_contra hn
    push Not at hn
    exact hM.1.2 ((iSup₂_le hn : R ≤ M) (hR u₀))
  have hj' : ∀ g u, j (σ.ρ g u) = ρ g (j u) := hj
  have k1 : LinearMap.ker (M.mkQ ∘ₗ j) = ⊥ := (irr _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hj']; exact hM.1.1 g _ hu).resolve_right fun e => hjM (by
      rintro _ ⟨z, rfl⟩
      simpa using (e ▸ Submodule.mem_top : z ∈ LinearMap.ker (M.mkQ ∘ₗ j)))
  have k2 : LinearMap.ker (M.mkQ ∘ₗ i) = ⊥ := (irr' _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hρ]; exact hM.1.1 g _ hu).resolve_right fun e => hM.1.2 (by
      simpa using (e ▸ Submodule.mem_top : u₀ ∈ LinearMap.ker (M.mkQ ∘ₗ i)))
  have big : i u₀ ∈ M ⊔ LinearMap.range j := by
    by_contra hn
    refine hjM (le_sup_right.trans (hM.2 ⟨fun g x hx => ?_, hn⟩ le_sup_left))
    obtain ⟨m, hm, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), ← hj']
    exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩
  have hu0 : u₀ ≠ 0 := fun e => hu₀ (by rw [e, map_zero])
  have s1 : (M ⊔ LinearMap.range j).comap i = ⊤ := (irr' _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hρ, ← e, map_add (f := _), ← hj']
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => hu0 (by
      have : u₀ ∈ (M ⊔ LinearMap.range j).comap i := big
      rwa [e, Submodule.mem_bot] at this)
  have s2 : (M ⊔ LinearMap.range i).comap j = ⊤ := (irr _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hj', ← e, map_add (f := _), ← hρ]
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 big
      have hz : z ∈ (M ⊔ LinearMap.range i).comap j := by
        rw [Submodule.mem_comap, eq_sub_of_add_eq' e', sub_eq_neg_add]
        exact Submodule.add_mem_sup (neg_mem hm) ⟨_, rfl⟩
      rw [e, Submodule.mem_bot] at hz
      rw [hz, map_zero, add_zero] at e'
      exact hM.1.2 (e' ▸ hm)
  have q : ∀ {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z] (a : Y →ₗ[ℂ] X) (b : Z →ₗ[ℂ] X),
      (M ⊔ LinearMap.range b).comap a = ⊤ → LinearMap.range (M.mkQ ∘ₗ a) ≤ LinearMap.range (M.mkQ ∘ₗ b) := by
    intro Y Z _ _ _ _ a b e
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 (show y ∈ (M ⊔ LinearMap.range b).comap a from e ▸ Submodule.mem_top)
    exact ⟨z, by simp [← e', (Submodule.Quotient.mk_eq_zero M).2 hm]⟩
  have er := le_antisymm (q j i s2) (q i j s1)
  let e := (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k1)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).symm)
  have he : ∀ u, (M.mkQ ∘ₗ i) (e u) = (M.mkQ ∘ₗ j) u := fun u =>
    congrArg Subtype.val ((LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).apply_symm_apply _)
  refine ⟨e, fun g u => LinearMap.ker_eq_bot.1 k2 ?_⟩
  have h1 := he u
  rw [he]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1 ⊢
  rw [hj', hρ, ← map_sub]
  exact hM.1.1 g _ (by simpa using neg_mem h1)
end
end
