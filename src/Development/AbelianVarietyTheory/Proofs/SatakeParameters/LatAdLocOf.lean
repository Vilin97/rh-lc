module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFirstFactorIntegersOntoLocalIntegers

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem ph_tensInt_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  intro F E _ _ _ _ _ n p G A hA v
  have h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y := by
    intro y
    show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y
    rw [hA v y]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v) := by
      refine (Subring.closure_le).2 ?_
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · obtain ⟨r, rfl⟩ := hx
        show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F
        have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r) := (RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)
        obtain ⟨q, hq, hev⟩ := h0
        let f : E →+* (A.pl v).1.adicCompletion F := (A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)
        have hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) := rfl
        have hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))) := by
          refine ⟨q.map (Int.castRingHom _), hq.map _, ?_⟩
          rw [Polynomial.eval₂_map, ← hf]
          have := congrArg f hev
          rw [map_zero, Polynomial.hom_eval₂] at this
          have e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp
              (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
          rw [e]
          exact this
        obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
        rw [← hz]
        exact z.2
      · show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F
        rw [h1]
        exact hy
    exact hle hs
  · intro x hx
    refine ⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩
    exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFirstFactorIntegersOntoLocalIntegersStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tensor_first_factor_integers_onto_local_integers : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  first | exact @GlobalTheory.TwV.ph_tensInt_onto | exact GlobalTheory.TwV.ph_tensInt_onto | (intros; apply GlobalTheory.TwV.ph_tensInt_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpEqImage

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem locSp_eq_image : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → LocInt A → ∀ v (Λ : Submodule (𝓞 E) (Fin n → E)) (z' : Fin n → G.P.Qq v), z' ∈ locSp (G.P.W v) (A.iw v) Λ ↔ ∃ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ, ∀ k, (A.eQ v).symm (A.ph v (z k)) = z' k := by
  intro F E _ _ _ _ _ n p G A hS hI v Λ z'
  have hph := GlobalTheory.T.tensor_first_factor_integers_onto_local_integers A hS v
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨fun k => inclE (F := F) _ (x k), Submodule.subset_span ⟨x, hx, rfl⟩, fun k => ?_⟩
      rfl
    | zero => exact ⟨0, Submodule.zero_mem _, fun k => by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨z₁, hz₁, e₁⟩ := h₁
      obtain ⟨z₂, hz₂, e₂⟩ := h₂
      refine ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, fun k => ?_⟩
      simp [e₁ k, e₂ k]
    | smul w y _ h =>
      obtain ⟨z, hz, e⟩ := h
      have hw : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) w) ∈ (A.pl v).1.adicCompletionIntegers F :=
        (hI v _).1 ⟨w, rfl⟩
      obtain ⟨s, hs, hse⟩ := hph.2 _ hw
      refine ⟨(⟨s, hs⟩ : intV E (A.pl v).1) • z, Submodule.smul_mem _ _ hz, fun k => ?_⟩
      show (A.eQ v).symm (A.ph v (s * z k)) = (w • y) k
      rw [map_mul, hse, map_mul, e k, RingEquiv.symm_apply_apply, Pi.smul_apply, Algebra.smul_def]
  · rintro ⟨z, hz, hzz⟩
    have key : ∀ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ,
        (fun k => (A.eQ v).symm (A.ph v (z k))) ∈ locSp (G.P.W v) (A.iw v) Λ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have h0 := Submodule.zero_mem (locSp (G.P.W v) (A.iw v) Λ)
        convert h0 using 1
        funext k
        simp
      | add y₁ y₂ _ _ h₁ h₂ =>
        have := Submodule.add_mem _ h₁ h₂
        simpa [Pi.add_def] using this
      | smul s y _ h =>
        obtain ⟨w, hw⟩ := (hI v ((A.eQ v).symm (A.ph v s))).2 (by simpa using hph.1 s.1 s.2)
        have := Submodule.smul_mem _ w h
        convert this using 1
        funext k
        show (A.eQ v).symm (A.ph v (s.1 * y k)) = _
        rw [Pi.smul_apply, Algebra.smul_def, hw, map_mul, map_mul]
    have := key z hz
    convert this using 1
    funext k
    exact (hzz k).symm

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdLocOf

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
end
end
