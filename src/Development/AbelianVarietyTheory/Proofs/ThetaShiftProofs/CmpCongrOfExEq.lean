module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.TotallySplit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkingsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exp_eq_of_isometry_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  first | exact @GlobalTheory.ArcPts.exp_eq_of_matching_markings | exact GlobalTheory.ArcPts.exp_eq_of_matching_markings | (intros; apply GlobalTheory.ArcPts.exp_eq_of_matching_markings <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FamilyUnifComponentConst

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory

theorem isHolTo_comp_fin_one {X : Scheme.{0}} {B : Set ℂ} {y : ℂ → (Sp ℂ ⟶ X)} (h : IsHolTo B y) :
    IsHolTo {b : Fin 1 → ℂ | b 0 ∈ B} (fun b => y (b 0)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun b : Fin 1 → ℂ => b 0) := continuous_apply (0 : Fin 1)
  refine ⟨h1.preimage hc, ?_⟩
  have hd : Differentiable ℂ (fun b : Fin 1 → ℂ => b 0) := differentiable_apply (0 : Fin 1)
  exact h2.comp hd.differentiableOn (fun b hb => hb)

theorem familyUnif_component_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)), IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ) → ∃ i, ∀ w : ℂ, T < w.im → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w := by
  intro E _ _ _ H _ D l Xo σ g ty Fu T yw hhol hσ
  classical
  set B : Set (Fin 1 → ℂ) := {b | T < (b 0).im} with hB
  have hBo : IsOpen B := isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
  have hBc : IsPreconnected B := by
    have hc : Convex ℝ B := by
      have := (convex_halfSpace_im_gt T).is_linear_preimage
        (f := fun b : Fin 1 → ℂ => b 0) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      exact this
    exact hc.isPreconnected
  have hy : IsHolTo B (fun b => yw (b 0)) := isHolTo_comp_fin_one hhol
  have hex : ∀ b : Fin 1 → ℂ, ∃ i : Fin Fu.n, b ∈ B → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw (b 0) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i, P, h⟩ := Fu.onto _ (hσ (b 0) hb)
      exact ⟨i, fun _ => ⟨P, h⟩⟩
    · exact ⟨⟨0, Fu.n_pos⟩, fun h => absurd h hb⟩
  choose c hc using hex
  have hcont : ContinuousOn c B := by
    intro b₀ hb₀
    obtain ⟨B', i, P, ho, hm, hsub, hP, hu⟩ := Fu.lift 1 B _ hBo (fun b hb => hσ (b 0) hb) hy b₀ hb₀
    have key : ∀ b ∈ B', c b = i := by
      intro b hb
      obtain ⟨Q, hQ, hQu⟩ := hc b (hsub hb)
      exact Fu.disj _ _ Q (P b) hQ (hP.1 b hb) (hQu.trans (hu b hb).symm)
    have hev : c =ᶠ[nhds b₀] fun _ => i := Filter.eventually_of_mem (ho.mem_nhds hm) key
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have h0 : (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I) ∈ B := by
    simp [hB]
  refine ⟨c (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I), fun w hw => ?_⟩
  have hwB : (fun _ : Fin 1 => w) ∈ B := hw
  rw [hBc.constant hcont h0 hwB]
  exact hc _ hwB

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FibreComparison

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq

section

@[expose] public section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem cmp_congr_of_ex_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (hk : 0 < k) (a b : (Fu.Di i).La)
    (hab : Fu.ex i P ((k : ℂ)⁻¹ • P a) = Fu.ex i P ((k : ℂ)⁻¹ • P b)) : ∃ e, a = b + k • e := by
  have h1 : Fu.ex i P ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) = 1 := by
    have h2 := Fu.ex_add i P hP ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) ((k : ℂ)⁻¹ • P b)
    rw [sub_add_cancel, hab] at h2
    exact mul_eq_right.1 h2.symm
  obtain ⟨e, he⟩ := (Fu.ex_ker i P hP _).1 h1
  refine ⟨e, hP.2.1 ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [map_add (f := _), map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_inv_smul₀ hk', smul_inv_smul₀ hk']
  abel

theorem cmp_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (A : AnArc (𝓞 E)) (w : ℂ) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y₀ : Sp ℂ ⟶ Xo.X) (hy : Fu.u i P = y₀)
    (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La)
    (hex : ∀ v, (Fu.ex i P (h v)).left = (π v).left) (hPg : ∀ u, P u = h (A.Pw w (gam u)))
    (k : ℕ) (hk : 0 < k) (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (a : (Fu.Di i).La) (la : A.La)
    (h1 : toUnit _ ≫ x = Fu.ex i P ((k : ℂ)⁻¹ • P a)) (h2 : toUnit _ ≫ x = π ((k : ℂ)⁻¹ • A.Pw w la)) :
    ∃ e, gam a = la + k • e := by
  subst hy
  have h3 : ∀ v, Fu.ex i P (h v) = π v := fun v => Over.OverMorphism.ext (hex v)
  obtain ⟨e, he⟩ := cmp_congr_of_ex_eq Fu i P hP k hk a (gam.symm la) (by
    rw [← h1, h2, ← h3, map_smul, hPg (gam.symm la), gam.apply_symm_apply])
  exact ⟨gam e, by rw [he, map_add (f := _), map_nsmul, gam.apply_symm_apply]⟩

theorem exists_cmp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (fr : ℂ → Xo.univ.t.PP.L.ι → A.V → ℂ) (laA laM : D.La → A.La), (inferInstance : StarRing (𝓞 E)) = H.starRing → (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ ∧ IsFibAt A Xo.univ.t lin cst w (yw w) (π w) (fr w) ∧ (Function.Surjective (π w) → (∀ v, toUnit _ ≫ Xo.univ.etaA v = π w ((l.A : ℂ)⁻¹ • A.Pw w (laA v))) ∧ ∀ v ∈ idealPart D l, toUnit _ ≫ Xo.univ.eta v = π w ((l.M : ℂ)⁻¹ • A.Pw w (laM v)))) → ∃ K : Cmp Fu A yw π laA laM, T ≤ K.T := by
  intro hL hL2 E _ _ _ H _ D l Xo σ g ty Fu A lin cst T yw π fr laA laM hstar hlin hrk hhol hw
  obtain ⟨i, hi⟩ := GlobalTheory.familyUnif_component_const E H D l Xo σ g ty Fu T yw hhol fun w h => (hw w h).1
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.fibre_comparison hL hL2 E H D l Xo σ g ty Fu A lin cst hlin hrk
  obtain ⟨T₁, hT₁⟩ := A.exists_BwMat_posDef
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

  have key : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La),
        IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w ∧ (∀ v, (Fu.ex i P (h v)).left = (π w v).left) ∧
        (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧
        (∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k) ∧
        (∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e) ∧
        ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e := by
    intro w hwT
    have h1 : T < w.im := lt_of_le_of_lt (le_max_left _ _) hwT
    have h2 : T₀ < w.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwT
    obtain ⟨P, hP, hu⟩ := hi w h1
    obtain ⟨-, hfib, hlev⟩ := hw w h1
    obtain ⟨hs, h, gam, hex, hPg, hEF, hact⟩ := hT₀ w i P (yw w) (π w) (fr w) h2 hP hu hfib
    obtain ⟨hA, hMM⟩ := hlev hs
    exact ⟨P, h, gam, hP, hu, hex, hPg, hEF, hact,
      fun v => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.A l.A_pos _ _ _ (Fu.ex_etaA i P hP v) (hA v),
      fun v hv => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.M hM _ _ _ (Fu.ex_eta i P hP v hv) (hMM v hv)⟩
  obtain ⟨-, h₁, gam₁, -, -, -, -, hEF₁, hact₁, hA₁, hM₁⟩ :=
    key (((max T (max T₀ T₁) + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  let Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun w =>
    (h₁.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (A.Pw w)).comp gam₁.toLinearMap.toAddMonoidHom
  have hPw : ∀ w u, Pw w u = h₁ (A.Pw w (gam₁ u)) := fun _ _ => rfl
  have hper : ∀ w : ℂ, max T (max T₀ T₁) < w.im → IsPeriod (Fu.Di i) ty (Pw w) := fun w hwT =>
    A.isPeriod (hT₁ w (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hwT)) (Fu.Di i) ty
      h₁.toLinearEquiv hact₁ gam₁.toAddEquiv (fun a x => gam₁.map_smul a x) hEF₁ (Pw w) (hPw w)
  have hmod : ∀ (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La) (k : ℕ) (a : (Fu.Di i).La) (la : A.La),
      (∃ e, gam a = la + k • e) → (∃ e, gam₁ a = la + k • e) → ∃ e, (gam.trans gam₁.symm) a = a + k • e := by
    rintro gam k a la ⟨e, he⟩ ⟨e₁, he₁⟩
    refine ⟨gam₁.symm (e - e₁), gam₁.injective ?_⟩
    rw [LinearEquiv.trans_apply, gam₁.apply_symm_apply, map_add (f := _), map_nsmul, gam₁.apply_symm_apply, he, he₁, smul_sub]
    abel
  have hrig : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      Fu.u i (Pw w) = yw w ∧ ∀ v, (Fu.ex i (Pw w) (h₁ v)).left = (π w v).left := by
    intro w hwT
    obtain ⟨P, h, gam, hP, hu, hex, hPg, hEF, -, hA, hMM⟩ := key w hwT
    obtain ⟨r1, r2⟩ := GlobalTheory.T.exp_eq_of_isometry_matching_markings E H D l Xo σ g ty Fu i P (Pw w) (gam.trans gam₁.symm)
      (h.symm.trans h₁).toLinearEquiv hstar hP (hper w hwT)
      (fun u v => by
        rw [← hEF₁, LinearEquiv.trans_apply, LinearEquiv.trans_apply, gam₁.apply_symm_apply, gam₁.apply_symm_apply, hEF])
      (fun v hv => hmod gam _ _ _ (hMM v hv) (hM₁ v hv)) (fun v => hmod gam _ _ _ (hA v) (hA₁ v))
      (fun u => by rw [hPw, hPg]; simp)
    refine ⟨r1.symm.trans hu, fun v => ?_⟩
    have := r2 (h v)
    rw [hex] at this
    rw [← this]
    simp
  exact ⟨⟨i, max T (max T₀ T₁), gam₁, h₁, hEF₁, hact₁, Pw, hPw, hper, fun w hwT => (hrig w hwT).1,
    fun w hwT => (hrig w hwT).2, hA₁, hM₁⟩, le_max_left _ _⟩

end GlobalTheory.ArcPts
end
end
end
