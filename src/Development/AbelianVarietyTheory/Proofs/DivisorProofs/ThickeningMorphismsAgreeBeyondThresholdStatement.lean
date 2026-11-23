module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  first | exact @GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | exact GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | (intros; apply GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatios

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

variable {X H Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem sval_eq_secRatio_mul {φ : K → (H ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ H) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (ha : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (secRatio a b) * sval a r z J := by
  have hc := hJ.mem φ r
  have hm : r z ∈ nonzeroLocus a ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨ha, hc⟩
  have e := congrArg (gs r z _) (secRatio_spec a b (fun k => J (r ≫ φ k)))
  rw [gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

theorem pullRatio_ι_comp {R : Type} [CommRing R] {M : ℕ} (P : H ⟶ PSpace R M) {U : H.Opens} {i : Fin (M + 1)}
    (hi : U ≤ P ⁻¹ᵁ chart R M i) (r : Z ⟶ H) (W : Z.Opens) (hW : W ≤ r ⁻¹ᵁ U)
    (h : ⊤ ≤ (W.ι ≫ r ≫ P) ⁻¹ᵁ chart R M i) (j : Fin (M + 1)) :
    pullRatio (W.ι ≫ r ≫ P) ⊤ i h j =
      (W.ι.appLE (r ⁻¹ᵁ U) ⊤ (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW))).hom
        ((r.app U).hom (pullRatio P U i hi j)) := by
  have hW' : ⊤ ≤ W.ι ⁻¹ᵁ (r ⁻¹ᵁ U) := W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW)
  rw [pullRatio_of_eq (Category.assoc W.ι r P).symm h ((hW'.trans ((W.ι ≫ r).preimage_mono hi))),
    ← appLE_pullRatio (W.ι ≫ r) hW', Scheme.Hom.app_eq_appLE, appLE_appLE]

end GlobalTheory.Mum.ThetaSep

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

theorem agree_near_of_minors : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ)
    (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤),
    IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J =
      sval (τ l) y.left z J * sval (τ j) y'.left z J) →
    ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  intro R _ _ D Y k N τ hτ hImm T y y' z J hJ hrel
  have hmono : Mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := inferInstance
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y.left z)))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y'.left z)))
  have ua : IsUnit (sval (τ j₀) y.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hj₀
  have ubi : IsUnit (sval (τ i) y'.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hi
  have ub : IsUnit (sval (τ j₀) y'.left z J) := by
    have h := hrel j₀ i
    have : IsUnit (sval (τ i) y.left z J * sval (τ j₀) y'.left z J) := h ▸ ua.mul ubi
    exact isUnit_of_mul_isUnit_right this
  have hj₀' : y'.left z ∈ nonzeroLocus (τ j₀) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).2 ub
  have hg : ∀ j, gs y.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) =
      gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) := by
    intro j
    have h := hrel j₀ j
    rw [sval_eq_secRatio_mul (τ j₀) (τ j) y.left z hJ hj₀,
      sval_eq_secRatio_mul (τ j₀) (τ j) y'.left z hJ hj₀'] at h
    refine ((ua.mul ub).mul_right_cancel ?_).symm
    calc _ = sval (τ j₀) y.left z J * (gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) *
          sval (τ j₀) y'.left z J) := by ring
      _ = _ := by rw [h]; ring
  have hW : ∀ j, ∃ W : T.left.Opens, z ∈ W ∧ ∃ (h₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀))
      (h₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀)),
      resG T.left h₁ ((y.left.app _).hom (secRatio (τ j₀) (τ j))) =
        resG T.left h₂ ((y'.left.app _).hom (secRatio (τ j₀) (τ j))) := by
    intro j
    have e := hg j
    rw [gs_eq _ z _ hj₀, gs_eq _ z _ hj₀'] at e
    obtain ⟨W, hzW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq T.left.presheaf z hj₀ hj₀' _ _ e
    exact ⟨W, hzW, leOfHom iU, leOfHom iV, e'⟩
  choose Wj hzWj h₁ h₂ heq using hW
  let W : T.left.Opens := Finset.univ.inf Wj
  have hzW : z ∈ W := Finset.inf_induction (p := fun U : T.left.Opens => z ∈ U) trivial
    (fun _ h _ h' => ⟨h, h'⟩) (fun j _ => hzWj j)
  have hWle : ∀ j, W ≤ Wj j := fun j => Finset.inf_le (Finset.mem_univ j)
  refine ⟨W, hzW, (cancel_mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ)).1 ?_⟩
  have hpre := toProj_preimage_chart Y.H.hom τ hτ j₀
  have hA : ∀ (r : T.left ⟶ Y.H.left), W ≤ r ⁻¹ᵁ nonzeroLocus (τ j₀) →
      ⊤ ≤ (W.ι ≫ r ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) ⁻¹ᵁ chart R N j₀ := fun r hr =>
    (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hr)).trans
      ((W.ι ≫ r).preimage_mono hpre.ge)
  have hy₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₁ j₀)
  have hy₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₂ j₀)
  simp only [Category.assoc]
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, j₀, hA _ hy₁, hA _ hy₂, fun j => ?_⟩
  · simp only [Category.assoc, toProj_str]
    rw [Over.w y, Over.w y']
  · rw [pullRatio_ι_comp _ hpre.ge _ W hy₁, pullRatio_ι_comp _ hpre.ge _ W hy₂, pullRatio_toProj]
    have hW₁ : ⊤ ≤ W.ι ⁻¹ᵁ Wj j := W.ι_preimage_self.ge.trans (W.ι.preimage_mono (hWle j))
    rw [← appLE_resG W.ι (h₁ j) hW₁, ← appLE_resG W.ι (h₂ j) hW₁, heq j]

end GlobalTheory.Mum.ThetaSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatiosStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ) (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J = sval (τ l) y.left z J * sval (τ j) y'.left z J) → ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  first | exact @GlobalTheory.Mum.ThetaSep.agree_near_of_minors | exact GlobalTheory.Mum.ThetaSep.agree_near_of_minors | (intros; apply GlobalTheory.Mum.ThetaSep.agree_near_of_minors <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThreshold

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_closedFibre_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (e : ℕ) (K : Type) [Field K] (a : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) e G).left), ∃ g : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) 0 G).left, g ≫ (fstG (maximalIdeal R) 0 G).left = a ≫ (fstG (maximalIdeal R) e G).left ∧ g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = a ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
  intro R _ _ _ G e K _ a
  let f := a ≫ (thickObj R (maximalIdeal R) e G).hom
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have hker : ∀ r ∈ maximalIdeal R ^ (0 + 1),
      (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r = 0 := by
    intro r hr
    rw [zero_add, pow_one] at hr
    have h1 : r ^ (e + 1) ∈ maximalIdeal R ^ (e + 1) := Ideal.pow_mem_pow hr _
    have h2 : (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r ^ (e + 1) = 0 := by
      rw [← map_pow, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h1, map_zero]
    exact pow_eq_zero_iff (Nat.succ_ne_zero e) |>.1 h2
  let ψ : R ⧸ maximalIdeal R ^ (0 + 1) →+* K := Ideal.Quotient.lift _ _ hker
  have hψ : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) ≫ φ := by
    ext r
    exact Ideal.Quotient.lift_mk (maximalIdeal R ^ (0 + 1)) (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) hker
  have hc : (a ≫ pullback.fst G.hom (thick R (maximalIdeal R) e)) ≫ G.hom =
      Spec.map (CommRingCat.ofHom ψ) ≫ thick R (maximalIdeal R) 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change f ≫ _ = _
    rw [← hφ, thick, thick, ← Spec.map_comp, ← Spec.map_comp, hψ]
  refine ⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, ?_⟩
  change pullback.lift _ _ hc ≫ pullback.snd _ _ ≫ _ = a ≫ pullback.snd _ _ ≫ _
  rw [pullback.lift_snd_assoc, ← hc, Category.assoc, pullback.condition]

theorem eq_of_germRatioAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro e k hk Z u u' hu s₀ i i'' z h
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  obtain ⟨hzi, hzi'', hu0, hu0', hrat⟩ := h
  set p := (fstG (maximalIdeal R) e G).left with hp
  have minor : ∀ j l, secGerm (u ≫ p) z (s j) i * secGerm (u' ≫ p) z (s l) i'' =
      secGerm (u ≫ p) z (s l) i * secGerm (u' ≫ p) z (s j) i'' := by
    intro j l
    have h1 := hrat (s j)
    have h2 := hrat (s l)
    apply (hu0.mul hu0').mul_left_cancel
    linear_combination (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s l) i'') * h1 -
      (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s j) i'') * h2

  let K := Z.residueField z
  let x : Spec (CommRingCat.of K) ⟶ Z := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hx : x pt = z := Scheme.fromSpecResidueField_apply z pt
  have minorx : ∀ j l, secGerm (x ≫ u ≫ p) pt (s j) i * secGerm (x ≫ u' ≫ p) pt (s l) i'' =
      secGerm (x ≫ u ≫ p) pt (s l) i * secGerm (x ≫ u' ≫ p) pt (s j) i'' := by
    intro j l
    have hi : (u ≫ p) (x pt) ∈ secChart U.LG.L i := hx ▸ hzi
    have hi'' : (u' ≫ p) (x pt) ∈ secChart U.LG.L i'' := hx ▸ hzi''
    have m := hx ▸ minor j l
    rw [secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u' ≫ p) pt _ hi'',
      secGerm_comp x (u' ≫ p) pt _ hi'', ← map_mul, ← map_mul, m]

  obtain ⟨g, hg1, hg2⟩ := exists_closedFibre_factor R G e K (x ≫ u)
  obtain ⟨g', hg1', hg2'⟩ := exists_closedFibre_factor R G e K (x ≫ u')
  let T : Over (Sp R) := Over.mk ((x ≫ u) ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e)
  have hgT : g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := hg2
  have hgT' : g' ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := by
    rw [hg2']; show _ = (x ≫ u) ≫ _
    simp only [Category.assoc, ← reassoc_of% hu]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g hgT
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g' hgT'
  set y := (Y.Φ T).symm ξ with hy
  set y' := (Y.Φ T).symm ξ' with hy'
  have hyξ : Y.Φ T y = ξ := Equiv.apply_symm_apply _ _
  have hyξ' : Y.Φ T y' = ξ' := Equiv.apply_symm_apply _ _
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB pt
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB pt
  obtain ⟨c, hc⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g y (hyξ ▸ hξ) k pt J J' hJ hJ'
  obtain ⟨c', hc'⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g' y' (hyξ' ▸ hξ') k pt J J' hJ hJ'
  have hv : ∀ j, secGerm (x ≫ u ≫ p) pt (s j) (fun _ => J ((x ≫ u ≫ p) ≫ 𝟙 _)) = c.val * sval (τ j) y.left pt J' := by
    intro j
    have := hc (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1, Category.assoc] at this
    exact this
  have hv' : ∀ j, secGerm (x ≫ u' ≫ p) pt (s j) (fun _ => J ((x ≫ u' ≫ p) ≫ 𝟙 _)) = c'.val * sval (τ j) y'.left pt J' := by
    intro j
    have := hc' (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1', Category.assoc] at this
    exact this
  have hi : (x ≫ u ≫ p) pt ∈ secChart U.LG.L i := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi
  have hi'' : (x ≫ u' ≫ p) pt ∈ secChart U.LG.L i'' := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi''
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (x ≫ u ≫ p) pt hi (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u ≫ p))
  obtain ⟨a', ha'⟩ := exists_unit_secGerm k (x ≫ u' ≫ p) pt hi'' (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u' ≫ p))
  have minorτ : ∀ j l, sval (τ j) y.left pt J' * sval (τ l) y'.left pt J' = sval (τ l) y.left pt J' * sval (τ j) y'.left pt J' := by
    intro j l
    have m := minorx j l
    rw [ha, ha, ha', ha', hv, hv, hv', hv'] at m
    apply (((a.isUnit.mul a'.isUnit).mul c.isUnit).mul c'.isUnit).mul_left_cancel
    linear_combination m
  obtain ⟨W, hW, hWy⟩ := GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios R D.toPre Y k N τ hτ himm T y y' pt J' hJ' minorτ
  have hWt : W = ⊤ := by
    exact eq_top_iff.2 fun q _ => (Subsingleton.elim (α := Spec (CommRingCat.of K)) q pt) ▸ hW
  subst hWt
  have : IsIso (⊤ : (T.left).Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hyy : y = y' := Over.OverMorphism.ext ((cancel_epi _).1 hWy)
  have hξξ : ξ = ξ' := by rw [← hyξ, ← hyξ', hyy]
  have hgg : g = g' := GlobalTheory.TorusCoord.IsPointOf.unique_left (U.gt 0) hξ (hξξ ▸ hξ')
  have hpp : (x ≫ u ≫ p) pt = (x ≫ u' ≫ p) pt := by
    rw [← Category.assoc, ← hg1, ← Category.assoc, ← hg1', hgg]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx] at hpp
  have : IsClosedImmersion p := by
    show IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e))
    have : IsClosedImmersion (thick R (maximalIdeal R) e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  exact p.isClosedEmbedding.injective hpp

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThresholdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.thickening_morphisms_agree_beyond_threshold : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  first | exact @GlobalTheory.Mum.eq_of_germRatioAgree | exact GlobalTheory.Mum.eq_of_germRatioAgree | (intros; apply GlobalTheory.Mum.eq_of_germRatioAgree <;> assumption)
end
end
