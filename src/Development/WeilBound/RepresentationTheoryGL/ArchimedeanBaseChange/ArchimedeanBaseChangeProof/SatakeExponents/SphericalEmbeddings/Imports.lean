module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2SphericalSwap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.IsSmoothCharUnr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ValuationDetKO

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExpEmb

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

theorem expEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.ExpEmb k := by
  intro n V _ _ π ξ hπ ⟨ℓ, hℓ0, hℓ⟩
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar fun i => unrChar k (ξ i)
  let ρ := (ofChar χ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨ℓ, fun g => LinearMap.ext fun v => by
      have h := hℓ ((leviTorus k (Fin n)).symm g) v
      have e : jacB π ((leviTorus k (Fin n)).symm g) = jac (points (Fin n)) π g := by
        show (jac (points (Fin n)) π) ((leviTorus k (Fin n)) ((leviTorus k (Fin n)).symm g)) = _
        rw [MulEquiv.apply_symm_apply]
      rw [e] at h
      refine h.trans ?_
      exact (ofChar_apply χ ((leviTorus k (Fin n)).symm g) (ℓ v)).symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hℓ0 ?_⟩
  have : φ = GlobalTheory.SmGL.Model.evalOne (points (Fin n)) (0 : π.IntertwiningMap (iP (k := k) ξ)) := by
    rw [← hf, h0]
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := congrArg (fun F => F (Submodule.Quotient.mk v)) this
  exact h1

end PositivityTheory.Rg.BcB.N3.Pee
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GaloisFixedAdelicMatricesDescend

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem extremeSph_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hC : SphConst k) (hS : SphEmb k) (hU : UniqSub k) : ExtremeSph k := by
  intro h0 n ξ hm V _ _ π hs hi ⟨f, hf⟩
  obtain ⟨W, _, _, σ, hσs, hσi, hσsph, hσq⟩ := hC n ξ
  obtain ⟨g, hg⟩ := hS n ξ hm W σ hσs hσi hσsph hσq
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσsph
  have hg0 : g ≠ 0 := fun e => hw0 (hg (by rw [e, map_zero]; rfl))
  obtain ⟨e⟩ := hU h0 n ξ hm V W π σ hi hσi f g hf hg0
  refine fun hb => hw0 ?_
  have hv : e.toLinearEquiv.symm w ∈ fixed π (KO k (Fin n)) := fun h => by
    have h1 := hwK h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h2 := e.isIntertwining' h
    have h3 := congrArg (fun F => F (e.toLinearEquiv.symm w)) h2
    simp only [LinearMap.comp_apply] at h3
    refine (h3.trans ?_).trans h1
    show σ h (e.toLinearEquiv (e.toLinearEquiv.symm w)) = σ h w
    rw [LinearEquiv.apply_symm_apply]
  rw [hb] at hv
  have h5 := congrArg e.toLinearEquiv ((Submodule.mem_bot ℂ).1 hv)
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

theorem galois_fixed_adelic_matrices_descend (hE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExpEmb k)
    (hX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExtremeSph k)
    (hL : SatLink) : N3 := by
  intro E _ _ w c n N h σ P ξ hq he hm
  obtain ⟨f, hf⟩ := hE (w.adicCompletion E) n P.V P.ρ ξ P.smooth he
  have hc : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact hL E w c n N h σ P ξ hq (hX (w.adicCompletion E) hc n ξ hm P.V P.ρ P.smooth P.irred ⟨f, hf⟩) ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.Pee
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.InjectiveOfIrred

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LFun
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3.Psl

open PositivityTheory.Rg.BcB.N3

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro y
  have e : {g : G | S.toRepresentation g y = y} = {g : G | ρ g (y : V) = y} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [e]
  exact hρ (y : V)

theorem injective_of_irred {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hi : ρ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Function.Injective f := by
  have := hi
  exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

theorem coe_mem_fixed {ρ : Representation ℂ G V} (S : Subrepresentation ρ) {K : Subgroup G}
    {s : S.toSubmodule} (hs : s ∈ fixed S.toRepresentation K) : s.1 ∈ fixed ρ K :=
  GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hs g hg)

theorem hI {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : G) (y : V) : f (ρ g y) = σ g (f y) :=
  Representation.IntertwiningMap.isIntertwining _ _ f g y


theorem satLink : SatLink := by
  intro E _ _ w c n N h σ P ξ hq hsph ⟨f, hf⟩
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hc : IsCompact (KO (w.adicCompletion E) (Fin n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isCompact_KO

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfi := injective_of_irred P.irred f hf

  have hy : f x ∈ fixed (iP (k := w.adicCompletion E) ξ) (KO _ (Fin n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hI f, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
  have hy0 : f x ≠ 0 := fun e => hx0 (hfi (e.trans (map_zero f).symm))
  have hφ : Formalism.UG.IsSpherical E w (fun i => (ξ i : ℂ)) (f x).1.1 :=
    (SphCompletion.isSpherical_iff E w n ξ _).2 ⟨f x, hy, rfl⟩
  have hφ0 : (f x).1.1 ≠ 0 := fun e => hy0 (Subtype.ext (Subtype.ext e))
  have hsatφ := isSatVecGL_of_isSpherical (w := w) hφ hφ0
  have hsatY : IsSatVecGL w (iP (k := w.adicCompletion E) ξ) (f x) (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) ((Submodule.subtype _).comp (Submodule.subtype _))
      (fun _ _ => rfl) (fun u v e => Subtype.ext (Subtype.ext e)) hsatφ
  have hsatX : IsSatVecGL w P.ρ x (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map f.toLinearMap (fun g y => hI f g y) hfi hsatY

  obtain ⟨S, q, hqs⟩ := hq
  obtain ⟨s0, hs0⟩ := hqs x
  have hSs : IsSmooth S.toRepresentation := isSmooth_sub (isSmooth_parInd _ _) S
  set s := GlobalTheory.LocGL.idem hSs hc s0 with hsdef
  have hqs' : q s = x := by
    rw [hsdef, GlobalTheory.LocGL.map_idem hSs P.smooth hc q s0, hs0, GlobalTheory.LocGL.idem_of_mem P.smooth hc hx]
  have hsfix : s ∈ fixed S.toRepresentation (KO _ (Fin n)) := GlobalTheory.LocGL.idem_mem hSs hc s0
  have htfix : s.1 ∈ fixed (locProd h w σ) (KGL w (n := n)) := by
    rw [hKO]
    exact coe_mem_fixed S hsfix
  have ht0 : s.1 ≠ 0 := fun e => hx0 (by rw [← hqs', show s = 0 from Subtype.ext e, map_zero])
  obtain ⟨B, hB, hsat⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (fun i => (σ i).smooth) (fun i => (σ i).irred) htfix ht0
  have hsatS : IsSatVecGL w S.toRepresentation s (∑ i, B i) :=
    IsSatVecGL.of_map (S.toSubmodule.subtype) (fun _ _ => rfl) Subtype.val_injective hsat
  have hsatX' : IsSatVecGL w P.ρ x (∑ i, B i) := by
    have := hsatS.map q.toLinearMap (fun g y => hI q g y) (by
      show q s ≠ 0
      rw [hqs']; exact hx0)
    rwa [show q.toLinearMap s = x from hqs'] at this
  exact ⟨fun i => (hB i).1, B, hB, hsatX'.unique hsatX⟩

end PositivityTheory.Rg.BcB.N3.Psl
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.UniqSub

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Pus

theorem uniqSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UniqSub k := uniqSub'

end PositivityTheory.Rg.BcB.N3.Pus
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Imports

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Final

open PositivityTheory.Rg.BcB.N3

theorem n3 : N3 :=
  Pee.galois_fixed_adelic_matrices_descend (fun k _ _ _ _ => Pee.expEmb k)
    (fun k _ _ _ _ => Pee.extremeSph_of k (Pee.sphConst k) (Pse.sphEmb k) (Pus.uniqSub k)) Psl.satLink

end PositivityTheory.Rg.BcB.N3.Final
end
end
