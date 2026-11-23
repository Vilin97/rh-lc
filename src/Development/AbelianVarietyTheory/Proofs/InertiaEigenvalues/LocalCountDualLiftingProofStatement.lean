module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestrictionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamilyStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.crystalline_potential_family : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  first | exact @GlobalTheory.Pass.LocDualU.main | exact GlobalTheory.Pass.LocDualU.main | (intros; apply GlobalTheory.Pass.LocDualU.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinsetStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.lengthModulo_span_le_of_forall_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  first | exact @GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | exact GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | (intros; apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllSubSumsOfLiftFamilyMatrixFamily

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem isSubFam_of_isSubSumOf {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL))
    (W A A' : GRep G Qp LL O) (hW : BlochKatoDuality.IsSubSumOf W.ρ A.ρ A'.ρ) (hA : IsSubFam Ms A)
    (hA' : IsSubFam Ms A') : IsSubFam Ms W := by
  obtain ⟨a, b, p, q, hp, hq, hinj⟩ := hW
  obtain ⟨a₁, x₁, p₁, hp₁, hinj₁⟩ := hA
  obtain ⟨a₂, x₂, p₂, hp₂, hinj₂⟩ := hA'
  let e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  let X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι :=
    Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)
  let P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL) :=
    Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))
  refine ⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩
  · intro j g v
    simp only [Function.comp]
    generalize e j = s
    rcases s with ⟨i, j'⟩ | ⟨i, j'⟩
    · simp only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]
    · simp only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]
  · intro v hv
    apply hinj v
    · intro i
      apply hinj₁
      intro j'
      have h := hv (e.symm (Sum.inl (i, j')))
      simpa [P] using h
    · intro i
      apply hinj₂
      intro j'
      have h := hv (e.symm (Sum.inr (i, j')))
      simpa [P] using h

end Gen

section OnePD

theorem liftAll_of_liftFam :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'
  intro W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA')
    (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF

end OnePD

end GlobalTheory.Pass.LocDual

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllSubSumsOfLiftFamilyMatrixFamilyStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  first | exact @GlobalTheory.Pass.LocDual.liftAll_of_liftFam | exact GlobalTheory.Pass.LocDual.liftAll_of_liftFam | (intros; apply GlobalTheory.Pass.LocDual.liftAll_of_liftFam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProof

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

namespace GlobalTheory.Pass.LocDual

theorem T2 {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {S S' : Submodule O M} (H : Submodule O M)
    (h : S ≤ S') : BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  unfold BlochKatoDuality.lenMod
  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right h H
  let f : ↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype →ₗ[O] ↥(S' ⊔ H) ⧸ H.comap (S' ⊔ H).subtype :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (fun x hx => hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have := (Submodule.Quotient.mk_eq_zero _).1 hz
  exact this



theorem main : StepLocDual := by
  intro D hLOC hBK hFont hPot i r hr Xs w hw hdeg n e hPF hLF k M hSub
  unfold LocBoundP
  apply GlobalTheory.T.lengthModulo_span_le_of_forall_finset
  intro F hF
  obtain ⟨X, hX, hle⟩ := GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice D hFont i r hr Xs w hw n hPF k M hSub F hF
  obtain ⟨hdrX, X', PX, hdX, hsX⟩ := GlobalTheory.T.potential_family_summand_restriction D hFont hPot i r hr Xs w hw n hPF X hX
  obtain ⟨hdrU, U', PU, hsU, LT', hdU, hrk⟩ := GlobalTheory.T.crystalline_potential_family D hFont hPot hBK i r hr Xs w hw hdeg n hPF k M hSub
  have hLift := GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily (Br.PD D.loc D.nbr i w hw) _ e X' U' hLF hsX hsU
  have hTw : IsTwistRep (1 : Br.G D.nbr i w hw →* (Br.LL D.nbr i w hw)ˣ)⁻¹ X.ρ X.ρ :=
    ⟨LinearEquiv.refl _ _, fun g x => by simp⟩
  have hHyp : BlochKatoDuality.Hyp (Br.PD D.loc D.nbr i w hw) X X (locU i w hw M hSub.1) X' U' 1 PX PU
      (Br.locLat D.nbr i w hw M) LT' e := ⟨hTw, hdrU, hdX, hdU, Or.inr ⟨hdrX, hLift⟩⟩
  obtain ⟨m, kk, hm, hk, hmk⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL) X X (locU i w hw M hSub.1) X' U' 1 PX PU
    (Br.locLat D.nbr i w hw M) LT' e hHyp
  refine (T2 _ hle).trans ?_
  change BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤ _
  have hm' : BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) = m := hm
  have hk' : lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = kk := hk
  rw [hm', hk']
  have : m ≤ 2 * k * e * kk :=
    hmk.trans ((Nat.mul_le_mul_right kk (Nat.mul_le_mul_left e hrk)).trans_eq (by ring))
  exact_mod_cast this

end GlobalTheory.Pass.LocDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProofStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.localCountDualLifting_proof : StepLocDual := by
  first | exact @GlobalTheory.Pass.LocDual.main | exact GlobalTheory.Pass.LocDual.main | (intros; apply GlobalTheory.Pass.LocDual.main <;> assumption)
end
end
