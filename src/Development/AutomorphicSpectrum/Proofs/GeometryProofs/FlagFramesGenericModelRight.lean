module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.RingTheory.LocalProperties.Reduced
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAtStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChartStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem chartSub_div_mem {F : Type} [Field F] {κ : Type} (x : κ → F) (c j : κ) :
    x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem chartSub_le_of_forall {F : Type} [Field F] {κ : Type} {x : κ → F} {c : κ} {T : Subring F}
    (h : ∀ j, x j / x c ∈ T) : chartSub x c ≤ T := by
  intro a ha
  have ha' : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := ha
  induction ha' using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    exact h j
  | algebraMap n => simpa using intCast_mem T n
  | add b d _ _ hb hd => exact T.add_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))
  | mul b d _ _ hb hd => exact T.mul_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))

theorem locSub_le_of {F : Type} [Field F] {R T : Subring F} {a : F} (h : R ≤ T) (ha : a⁻¹ ∈ T) :
    locSub R a ≤ T :=
  Subring.closure_le.2 (Set.union_subset h (Set.singleton_subset_iff.2 ha))

theorem flagCoord_div_eq {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type}
    (x : κ → Ω) {S : Type} [Fintype S] {r n m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω}
    {c₀ : κ} (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (hx : x c₀ ≠ 0)
    (h : ∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) (k : κ)
    (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc ((k, J') : FlagIx κ n r) / flagCoord κ x φ cc ((c₀, J) : FlagIx κ n r) =
      algebraMap Ω (GenField Ω r) (x k / x c₀) *
        ∏ q : (Σ s, Fin (r s)), stepMinor (flagB M T q.1) q.2 (J' q) / stepMinor (flagB M T q.1) q.2 (J q) := by
  have hi : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := (map_ne_zero _).2 hx
  rw [flagCoord_eq x h k J', flagCoord_eq x h c₀ J, map_div₀, mul_div_mul_comm,
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hi))

theorem chartRing_eq_ratioRing : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type)
    (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω)
    (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 →
    g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) →
    (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) →
    algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧
    locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) =
      ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  intro Ω _ E _ _ κ x S _ r n m φ cc M T c₀ J g hx hg hg0 h hJ
  classical
  set A := chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) with hA
  have hdiv := fun k J' => flagCoord_div_eq (m := m) x J hx h k J'

  have h1 : ∀ k, algebraMap Ω (GenField Ω r) (x k / x c₀) ∈ A := by
    intro k
    have e := hdiv k J
    have e1 : ∏ q : (Σ s, Fin (r s)),
        stepMinor (flagB M T q.1) q.2 (J q) / stepMinor (flagB M T q.1) q.2 (J q) = 1 :=
      Finset.prod_eq_one fun q _ => div_self (hJ q)
    rw [e1, _root_.mul_one] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ((k, J) : FlagIx κ n r)

  have h2 : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A := by
    intro q J'
    have e := hdiv c₀ (Function.update J q J')
    rw [div_self hx, map_one, _root_.one_mul, Finset.prod_div_distrib,
      prod_update_div (β := fun q : (Σ s, Fin (r s)) => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => stepMinor (flagB M T q.1) q.2 b) J hJ q J'] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)
      ((c₀, Function.update J q J') : FlagIx κ n r)
  have himg : chartSub x c₀ ≤ A.comap (algebraMap Ω (GenField Ω r)) :=
    chartSub_le_of_forall fun j => h1 j
  have hgA : algebraMap Ω (GenField Ω r) g ∈ A := himg hg
  refine ⟨hgA, le_antisymm ?_ ?_⟩
  ·
    set R' := locSub (chartSub x c₀) g with hR'
    have him : ∀ b ∈ R', algebraMap Ω (GenField Ω r) b ∈ ratioRing R' (flagB M T) J := fun b hb =>
      Subring.subset_closure (Or.inl ⟨b, hb, rfl⟩)
    refine locSub_le_of (chartSub_le_of_forall ?_) ?_
    · rintro ⟨k, J'⟩
      rw [hdiv k J']
      refine Subring.mul_mem _ (him _ (le_locSub _ _ (chartSub_div_mem x c₀ k))) ?_
      exact Subring.prod_mem _ fun q _ => Subring.subset_closure (Or.inr ⟨q, J' q, rfl⟩)
    · rw [← map_inv₀]
      exact him _ (inv_mem_locSub _ _)
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨b, hb, rfl⟩
      have hle : locSub (chartSub x c₀) g ≤
          (locSub A (algebraMap Ω (GenField Ω r) g)).comap (algebraMap Ω (GenField Ω r)) := by
        refine locSub_le_of (himg.trans fun a ha => le_locSub _ _ ha) ?_
        show algebraMap Ω (GenField Ω r) g⁻¹ ∈ locSub A (algebraMap Ω (GenField Ω r) g)
        rw [map_inv₀]
        exact inv_mem_locSub _ _
      exact hle hb
    · rintro _ ⟨q, J', rfl⟩
      exact le_locSub _ _ (h2 q J')

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegularStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.chart_frame_matrix_regular : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 → g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧ locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) = ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem val_appLE_of_dominates {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : Dominates ξ' ξ f i) {U : X.Opens} {W : X'.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : genPt ξ' ∈ W)
    (hU : genPt ξ ∈ U) (t : Γ(X, U)) :
    (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) =
      i ((X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t) := by
  have hfq : f (genPt ξ') ∈ U := e hW
  have hp : genPt ξ ⤳ f (genPt ξ') := by rw [RegAtDom.map_genPt hd]
  have h := RegAtDom.genMap_stalkMap hd (genPt ξ') specializes_rfl hp
    ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t)
  have l1 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ f.stalkMap (genPt ξ') =
      f.appLE U W e ≫ X'.presheaf.germ W (genPt ξ') hW := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have l2 : X'.presheaf.germ W (genPt ξ') hW ≫ X'.presheaf.stalkSpecializes specializes_rfl =
      X'.presheaf.germ W (genPt ξ') hW := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have l3 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ X.presheaf.stalkSpecializes hp =
      X.presheaf.germ U (genPt ξ) hU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have a1 : (f.stalkMap (genPt ξ')).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t) :=
    congrArg (fun g => g.hom t) l1
  have a2 : ∀ s, (X'.presheaf.stalkSpecializes specializes_rfl).hom
      ((X'.presheaf.germ W (genPt ξ') hW).hom s) = (X'.presheaf.germ W (genPt ξ') hW).hom s :=
    fun s => congrArg (fun g => g.hom s) l2
  have a3 : (X.presheaf.stalkSpecializes hp).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU).hom t := congrArg (fun g => g.hom t) l3
  rw [a1] at h
  have b1 : genMap ξ' ⟨genPt ξ', specializes_rfl⟩ ((X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t)) =
      (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) := by
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom (a2 _)
  have b2 : genMap ξ ⟨f (genPt ξ'), hp⟩ ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t := by
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom a3
  rw [← b1, h, b2]

theorem smooth_of_pieces : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i →
    (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C),
      IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧
      ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hg hg' hd h
  refine (HasRingHomProperty.iff_exists_appLE (P := @Smooth) (Q := RingHom.Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1).2 fun p' => ?_
  obtain ⟨U, W, R, C, hRC, hU, hW, e, hp, hs⟩ := h p'
  refine ⟨⟨U, hU.affine⟩, ⟨W, hW.affine⟩, hp, e, ?_⟩
  have hWg : genPt ξ' ∈ W := (hW.spec p' hp).mem_open W.isOpen hp
  have hUg : genPt ξ ∈ U := by
    have h1 : f (genPt ξ') ∈ U := e hWg
    rwa [RegAtDom.map_genPt hd] at h1
  obtain ⟨injU, ranU⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hg U hUg hU.spec
  obtain ⟨injW, ranW⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X' Ω' ξ' hg' W hWg hW.spec
  have memR : ∀ t, (X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom t ∈ R :=
    fun t => (hU.ring _).2 ((ranU _).1 ⟨t, rfl⟩)
  have memC : ∀ t, (X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom t ∈ C :=
    fun t => (hW.ring _).2 ((ranW _).1 ⟨t, rfl⟩)
  let eU : Γ(X, U) ≃+* R := RingEquiv.ofBijective
    ((X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom.codRestrict R memR)
    ⟨fun a b hab => injU (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranU r.1).2 ((hU.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  let eW : Γ(X', W) ≃+* C := RingEquiv.ofBijective
    ((X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom.codRestrict C memC)
    ⟨fun a b hab => injW (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranW r.1).2 ((hW.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  have hval : ∀ t, eW ((f.appLE U W e).hom t) =
      ((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)) (eU t) :=
    fun t => Subtype.ext (val_appLE_of_dominates hd e hWg hUg t)
  have key : (f.appLE U W e).hom = (eW.symm : C →+* Γ(X', W)).comp
      (((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)).comp (eU : Γ(X, U) →+* R)) :=
    RingHom.ext fun t => (eW.symm_apply_eq.2 (hval t).symm).symm
  show RingHom.Smooth (f.appLE U W e).hom
  rw [key]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp (RingHom.Smooth.of_bijective eU.bijective) hs)
    (RingHom.Smooth.of_bijective eW.symm.bijective)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmoothStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.dominating_pieces_smooth : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i → (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C), IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧ ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem isPiece_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

theorem coordTie_int_inst {X : Scheme.{0}} {F : Type} [Field F] {ξ : Spec (CommRingCat.of F) ⟶ X} {κ : Type} {x : κ → F}
    (inst : Algebra ℤ F) (h : @CoordTie X F _ ℤ _ inst ξ κ x) : @CoordTie X F _ ℤ _ (Ring.toIntAlgebra F) ξ κ x := by
  rwa [Subsingleton.elim inst (Ring.toIntAlgebra F)] at h

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b g : F} (hb : b ∈ R) (h : a * b = g) (hg : g ≠ 0) :
    locSub R a ≤ locSub R g := by
  refine (Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)
  rintro _ rfl
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hg)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (h ▸ hg)
  have e : a⁻¹ = b * g⁻¹ := by rw [← h]; field_simp
  rw [SetLike.mem_coe, e]
  exact (locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)

theorem flag_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch
  classical
  have hi : Function.Injective (algebraMap Ω (GenField Ω r)) := (algebraMap Ω (GenField Ω r)).injective
  refine GlobalTheory.T.dominating_pieces_smooth X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)
  let P' : Cpt ξ' := ⟨p', hall' p'⟩
  obtain ⟨⟨c₀, J⟩, hcJ⟩ := hT'.cover P'
  have hy0 : flagCoord κ x φ c (c₀, J) ≠ 0 := hcJ.1
  have hx0 : x c₀ ≠ 0 := by
    intro h0
    apply hy0
    simp [flagCoord, h0]

  have hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' →
      InChart ξ x c₀ ⟨f Q'.1, hall _⟩ := by
    intro Q' hQ
    refine (hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩
    have h := hQ.2 ((k, J) : FlagIx κ n r)
    have hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0 := by
      intro h0
      apply hy0
      simp [flagCoord, h0]
    have e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) =
        algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀) := by
      simp only [flagCoord]
      have : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
      field_simp
    rwa [e] at h
  let P : Cpt ξ := ⟨f p', hall _⟩
  have h2 : InChart ξ x c₀ P := hover P' hcJ
  have hfr := fun s => GlobalTheory.T.twisted_frame_in_chart X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2
  choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr
  let g₀ : Ω := ∏ s, g s
  have hg₀R : g₀ ∈ chartSub x c₀ := Subring.prod_mem _ fun s _ => hgR s
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1
  have hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q := fun a ha Q hQ =>
    (hT.ring c₀ hx0 a).1 ha Q hQ
  have hg₀inv : g₀⁻¹ ∈ regAt ξ P := by
    have : g₀⁻¹ = ∏ s, (g s)⁻¹ := by simp [g₀]
    rw [this]
    exact Subring.prod_mem _ fun s _ => (hgu s).2.2
  have hg₀u : unitAt ξ P g₀ := ⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩
  let R : Subring Ω := locSub (chartSub x c₀) g₀
  have hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R := fun s =>
    locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s')
      (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0
  have hRP : ∀ a ∈ R, a ∈ regAt ξ P := by
    have : R ≤ regAt ξ P := (Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2)
      (by rintro _ rfl; exact hg₀inv))
    exact this
  obtain ⟨hPh, hdom1, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'
  have hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P' := fun a ha => hdom1 a (hRP a ha)
  haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1
  have hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _ :=
    fun k J' => flagCoord_eq (m := m) x hφ k J'
  have hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
  have hprod0 := hscale c₀ J
  have hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0 := by
    intro q h0
    apply hy0
    rw [hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]
  have hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P' := by
    intro q J'
    have h := hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)
    rw [hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax,
      prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J
        (fun q => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hax)) (hβ0 q)) q J',
      mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hax))] at h
    exact h
  obtain ⟨t, htR, ht0, htO, htiO, hmap, hsm⟩ := GlobalTheory.T.frame_matrices_regular_generic Ω S r n R (regAt ξ' P') T M N J hRO hT0
    (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ
  obtain ⟨hgA, hAeq⟩ := GlobalTheory.T.chart_frame_matrix_regular Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0
  obtain ⟨U₀, hU₀, hU₀m⟩ := isPiece_chart hT hx0
  obtain ⟨U₁, hU₁, hU₁m⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0
  obtain ⟨W₀, hW₀, hW₀m⟩ := isPiece_chart (coordTie_int_inst _ hT') hy0
  have hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0 := by simpa using hg₀0
  obtain ⟨W₁, hW₁, hW₁m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0
  rw [hAeq] at hW₁
  obtain ⟨W₂, hW₂, hW₂m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0
  refine ⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩
  · intro q' hq'
    let Q' : Cpt ξ' := ⟨q', hall' q'⟩
    have e1 := ((hW₂m Q').1 hq').1
    obtain ⟨e2, e3⟩ := (hW₁m Q').1 e1
    have e4 := (hW₀m Q').1 e2
    have e5 := hover Q' e4
    obtain ⟨h', -, hun⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'
    exact (hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩
  · refine (hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩
    rw [← map_inv₀]
    exact hRO _ (inv_mem_locSub _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end
end
