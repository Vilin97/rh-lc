module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DatumExistsPeriod
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTripleStatement
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHermFormCurve
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsExpPush
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamily
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultTensorOfFinrank
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MapRtEqNegIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open PureTypeVector in
theorem cmDatum_form_sqrtNegD_pure_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {ρ : ℂ}
    (hty : ∀ i, ty i (H.rt : E) = ρ) {x : D.La} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ρ.im * r := by
  obtain ⟨hlin, hinj, -, -, Hm, hH, hpos, hEF⟩ := hP
  have hw0 : Pe (H.w0 • x) = ((1 + ρ) / 2) • Pe x := by
    funext i
    rw [hlin, Pi.smul_apply, smul_eq_mul]
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simpa [map_ofNat] using this
    have h3 := congrArg (ty i) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hty i] at h3
    rw [← h3]; ring
  set r : ℝ := (hermForm Hm (Pe x) (Pe x)).re with hr
  have hre : hermForm Hm (Pe x) (Pe x) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [hermForm_self_im hH])
  have hr0 : 0 < r := hpos _ fun h => hx (hinj (by rw [h, map_zero]))
  refine ⟨r / 2, by positivity, ?_⟩
  rw [← hEF, hw0]
  have := hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [this, hre]
  simp
  ring

theorem definite_datum_form_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ),
      (D.q = 0 ∧ 0 < ((ε : ℤ) : ℝ) * H.rt0.im) ∨ (D.p = 0 ∧ ((ε : ℤ) : ℝ) * H.rt0.im < 0) →
      ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := by
  intro E _ _ _ H D ε h x hx
  obtain ⟨g, ty, hty⟩ : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
    have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩⟩
  obtain ⟨Pe, hP⟩ := datum_exists_period E H D g ty hty
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := fun i =>
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    Nat.card_pos.ne'
  have key : ∃ ρ : ℂ, (∀ i, ty i (H.rt : E) = ρ) ∧ 0 < ((ε : ℤ) : ℝ) * ρ.im := by
    rcases h with ⟨hq, hε⟩ | ⟨hp, hε⟩
    · refine ⟨H.rt0, fun i => ?_, hε⟩
      by_contra hne
      exact hcard i (((hty (ty i)).2 hne).trans hq)
    · refine ⟨-H.rt0, fun i => ?_, by simpa using hε⟩
      have hne : ty i (H.rt : E) ≠ H.rt0 := fun he => hcard i (((hty (ty i)).1 he).trans hp)
      have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
        have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
        simpa using this
      have h3 : ty i (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, h2, H.sqrt_neg_disc_sq]; simp
      exact (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left hne
  obtain ⟨ρ, hρ, hε⟩ := key
  obtain ⟨r, hr, hE⟩ := cmDatum_form_sqrtNegD_pure_period D hP hρ hx
  have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((D.EF (H.w0 • x) x : ℤ) : ℝ) := by
    rw [hE, ← _root_.mul_assoc]; exact mul_pos hε hr
  exact_mod_cast this

end GlobalTheory.CM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  first | exact @GlobalTheory.CM.PeriodModel.exists_model | exact GlobalTheory.CM.PeriodModel.exists_model | (intros; apply GlobalTheory.CM.PeriodModel.exists_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLaws

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.ExObj

theorem additive_ext {V L M : Type} [AddCommGroup V] [Module ℂ V] [Group M] {P : L → V}
    (hP : Submodule.span ℝ (Set.range P) = ⊤) {u v : V → M} (hu : ∀ z w, u (z + w) = u z * u w)
    (hv : ∀ z w, v (z + w) = v z * v w) (h : ∀ a (c : ℂ), u (c • P a) = v (c • P a)) (z : V) : u z = v z := by
  have u0 : u 0 = 1 := by simpa using hu 0 0
  have v0 : v 0 = 1 := by simpa using hv 0 0
  have key : ∀ c : ℂ, u (c • z) = v (c • z) := by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
    | zero => intro c; rw [smul_zero, u0, v0]
    | add x y _ _ hx hy => intro c; rw [smul_add, hu, hv, hx, hy]
    | smul r x _ hx => intro c; rw [← Complex.coe_smul, smul_smul]; exact hx _
  simpa using key 1

theorem exists_sum {J V L : Type} [Fintype J] [AddCommGroup V] [Module ℂ V] {W : J → Type} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] (F : ∀ j, W j →ₗ[ℂ] V) {P : L → V} (hP : Submodule.span ℝ (Set.range P) = ⊤) {n : ℕ}
    (hn : 0 < n) (h : ∀ a, ∃ x : ∀ j, W j, n • P a = ∑ j, F j (x j)) (z : V) : ∃ x : ∀ j, W j, z = ∑ j, F j (x j) := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
  have sm : ∀ (c : ℂ) (y : V), (∃ x : ∀ j, W j, y = ∑ j, F j (x j)) → ∃ x : ∀ j, W j, c • y = ∑ j, F j (x j) := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨fun j => c • x j, by simp [Finset.smul_sum]⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := sm (n : ℂ)⁻¹ _ (h a)
    rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul] at this
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩
  | smul r x _ hx => rw [← Complex.coe_smul]; exact sm _ _ hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_ten_exp (hT : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R] [IsNoetherianRing R] {ω : R}
    (C : Ell H R ω) (σ : R →+* ℂ) {ω' : ℂ} (C' : Ell H ℂ ω') (π : C'.P.A.left ⟶ C.P.A.left)
    (u₀ : HolUnif C'.P.A C'.P.L C'.P.g) (c : ℂ) (D : Datum H) (ε : ℤˣ) (hm : EllMap C' C σ π) (hc : c ≠ 0)
    (hu : PureType.IsQuadLattice u₀.Λ H.d c) (hε : 0 < ((ε : ℤ) : ℝ) * ω'.im)
    (hD : (D.q = 0 ∧ 2 * ω' - 1 = H.rt0) ∨ (D.p = 0 ∧ 2 * ω' - 1 = -H.rt0)) :
    ∃ (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (g : ℕ) (ty : Fin g → (E →+* ℂ))
      (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)),
      IsKForm D ε h ∧ IsTypeFn H D.p D.q ty ∧ IsExp T σ D ty P e ∧
      (∀ a (z : ℂ), (e (z • P a)).left = (u₀.ex (fun _ => c * z)).left ≫ π ≫ (t.ten.tmul a).left) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : D.La →+ V), (∀ a, f (H.w0 • a) = ω' • f a) →
        ∃ F : (Fin g → ℂ) →ₗ[ℂ] V, ∀ a, F (P a) = f a := by
  obtain ⟨h, hh, -⟩ := exists_kForm E H D ε
  have hpos := definite_datum_form_pos E H D ε (by
    rcases hD with ⟨a, b⟩ | ⟨a, b⟩
    · refine Or.inl ⟨a, ?_⟩
      have := congrArg Complex.im b
      simp at this
      rw [← this]; linarith
    · refine Or.inr ⟨a, ?_⟩
      have := congrArg Complex.im b
      simp at this
      rw [show H.rt0.im = -(2 * ω'.im) by linarith]; linarith)
  obtain ⟨T, ⟨t⟩, -⟩ := GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple hL E H R ω C D ε _ hh hpos
  obtain ⟨T', m, -⟩ := PAT.exists_pullback E H _ _ (spMap σ) T
  obtain ⟨t', ht'⟩ := isTen_baseChange E H R ω C D _ T t ℂ ω' C' σ π T' m hm
  obtain ⟨g, ty, P, e', hty, he', htie, hF⟩ := TenExp.exists_isExp_of_isTen hT hL E H ω' C' u₀ c D ε _ T' t' hc hu hε hh hD
  obtain ⟨e, he, hee⟩ := exists_isExp_push E H R σ T T' m D g ty P e' he'
  refine ⟨_, T, t, g, ty, P, e, hh, hty, he, fun a z => ?_, hF⟩
  rw [hee, htie, Over.comp_left, Category.assoc, ht']

theorem hasType_of_moduli {D : Datum H} {l : Level H} (Xo : Moduli D l) (K₁ : IntermediateField ℚ ℂ) [NumberField K₁]
    (hk : KA l ≤ K₁) (ρ : 𝓞 K₁) (hρ : ((ρ : K₁) : ℂ) = H.rt0) (B : SAB H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X)
    (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K₁) K₁)))
    (hy : y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom) : HasType H B.act ρ D.p D.q := by
  refine (hasType_baseChange E H _ _ _ B t₀ m' ρ D.p D.q).2 (fun k _ β hβ => ?_) (fun k _ _ β _ τ => ?_)
  · exact ⟨IsFractionRing.lift hβ, RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x, RingHom.injective _⟩
  · have h := (Xo.univ.geom k (spMap β ≫ y) (β.comp (IntermediateField.inclusion hk).toRingHom) (by
      rw [Category.assoc, hy]; exact (Spec.map_comp _ _).symm)).1 τ
    have e : (β.comp (IntermediateField.inclusion hk).toRingHom) (baseKA l).ρ = β (algebraMap (𝓞 K₁) K₁ ρ) :=
      congrArg β (Subtype.ext hρ.symm)
    rw [e, ← LiePull.lieMult_pull _ _ _ _ _ y m.cm.F _ t₀.act m.cart m.act,
      ← LiePull.lieMult_pull _ _ _ _ _ y m.cm.F _ t₀.act m.cart m.act] at h
    exact h

theorem cmExists : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt →
    CMExistsSt := by
  intro h1 h2 hT hL hL2 hH hK E _ _ _ H D l Xo g ty FU i Pe hP Z k hkf
  obtain ⟨⟨k₀, hk₀, hconj⟩, hsplit, -⟩ := splits_basic E
  obtain ⟨K₁, inst, hk, ω, C, ε, h, B, y, t₀, m, m', ψ, ω', C', π, u₀, c, hkK, hy, hyu, hb⟩ :=
    GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre h1 h2 hT hL hL2 hH hK E H D l Xo g ty FU i Pe hP _ _ Z (k ⊔ k₀) inferInstance
  choose hω hε hh hψ hm hc hu htie using hb
  set σ : 𝓞 K₁ →+* ℂ := (algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁) with hσ
  have hσi : Function.Injective σ := (algebraMap K₁ ℂ).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hσω : ∀ b, σ (2 * ω b - 1) = if b then H.rt0 else -H.rt0 := fun b => by
    rw [map_sub, map_mul, map_ofNat, map_one, (hm b).1, hω]
  choose h₁ T t gA tyA PA e hh₁ hty he hee hF using fun b : Bool =>
    exists_ten_exp hT hL (C b) σ (C' b) (π b) (u₀ b) (c b) (Z.D₁ b) (ε b) (hm b) (hc b) (hu b) (hε b) (by
      cases b
      · exact Or.inr ⟨Z.sigM.1, hω false⟩
      · exact Or.inl ⟨Z.sigP.2, hω true⟩)
  choose Φ hΦl hΦt hΦp using fun j : Fin D.p ⊕ Fin D.q =>
    exists_famLift E H _ _ (C j.isLeft) (Z.D₁ j.isLeft) (FU.Di i) (ε j.isLeft) (h₁ _) (h _) (T _) B (t _) _ (ψ j.isLeft)
      ((Z.f j).codRestrict _ (Z.pure j)) (Z.hh j) (hh₁ _) (hh _) (Z.form j) (hψ _)
  choose F hFP using fun j : Fin D.p ⊕ Fin D.q =>
    hF j.isLeft (Fin g → ℂ) (Pe.comp (Z.f j).toAddMonoidHom) (fun a => by
      show Pe (Z.f j (H.w0 • a)) = _ • Pe (Z.f j a)
      rw [map_smul, PureType.period_w0_smul hP (Z.pure j a), ← hω]
      congr 1
      ring)
  replace hFP : ∀ j a, F j (PA _ a) = Pe (Z.f j a) := hFP
  obtain ⟨κ', hκ'⟩ := LiePull.exists_pushEquiv m'.cart (Over.mk (spMap (algebraMap K₁ ℂ))) (spMap σ)
    (Spec.map_comp (CommRingCat.ofHom (algebraMap (𝓞 K₁) K₁)) (CommRingCat.ofHom (algebraMap K₁ ℂ)))
  obtain ⟨κ, hκ⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (algebraMap K₁ ℂ))) (FU.u i Pe) hyu.symm
  have hadd : ∀ (j : Fin D.p ⊕ Fin D.q) z w, e _ (z + w) ≫ Φ j = (e _ z ≫ Φ j) * (e _ w ≫ Φ j) := fun j z w => by
    have := (hΦl j).1
    rw [(he _).2.2.1, MonObj.mul_comp]
  have tie : ∀ (j : Fin D.p ⊕ Fin D.q) z, κ (κ'.symm (e _ z ≫ Φ j)) = FU.ex i Pe (F j z) := fun j z => by
    refine additive_ext (he j.isLeft).1.2.2.2.1 (u := fun z => κ (κ'.symm (e _ z ≫ Φ j)))
      (v := fun z => FU.ex i Pe (F j z)) (fun z w => ?_) (fun z w => ?_) (fun a s => ?_) z
    · simp only [hadd, map_mul]
    · simp only [map_add (f := _), FU.ex_add i Pe hP]
    · apply Over.OverMorphism.ext
      simp only [map_smul, hFP, hκ]
      refine htie j.isLeft ⟨Z.f j a, Z.pure j a⟩ s _ (Over.w _) ?_
      refine (hκ' _).symm.trans ?_
      rw [κ'.apply_symm_apply, Over.comp_left, hee, Category.assoc, Category.assoc, ← Over.comp_left, hΦt]
      rfl
  have hρ : σ (2 * ω true - 1) = H.rt0 := hσω true
  have hsq : (2 * ω true - 1) ^ 2 = -(H.d : 𝓞 K₁) := hσi (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hneg : 2 * ω false - 1 = -(2 * ω true - 1) := hσi (by rw [map_neg, hρ, hσω]; rfl)
  have tP := hasType_of_isTen hL.polBaseChange E H _ _ (C true) _ _ _ ⟨t true⟩
  have tM := hasType_of_isTen hL.polBaseChange E H _ _ (C false) _ _ _ ⟨t false⟩
  rw [Z.sigP.1, Z.sigP.2] at tP
  rw [Z.sigM.1, Z.sigM.2, hneg] at tM
  refine ⟨K₁, inst, hk, 2 * ω true - 1,
    { split := hsplit K₁ fun τ a => hkK ((le_sup_right : k₀ ≤ k ⊔ k₀) (hconj τ a))
      ρ_sq := hsq
      A := T
      B := B
      typeP := tP
      typeM := (hasType_neg_iff E H _ _ _ _ 0 1 hsq).2 tM
      typeB := hasType_of_moduli Xo K₁ hk (2 * ω true - 1) hρ B.t y t₀ m m' hy
      hh := Z.hh
      φ := Φ
      lin := hΦl
      onto := fun w => ?_
      weil := fun j => ?_ }, y, t₀, m, m', gA, tyA, PA, e, F, le_sup_left.trans hkK, hρ, rfl, hy, hyu,
    fun b => ⟨hty b, he b⟩, hFP, fun j z x hx hxe => ?_⟩
  · obtain ⟨v, hv⟩ := FU.ex_onto i Pe hP (κ (κ'.symm w))
    obtain ⟨n, hn, hs⟩ := Z.span
    obtain ⟨z, rfl⟩ := exists_sum F hP.2.2.2.1 hn (fun a => by
      obtain ⟨x, hx⟩ := hs a
      exact ⟨fun j => PA _ (x j), by simp only [hFP, ← map_sum, ← hx, map_nsmul]⟩) v
    refine ⟨fun j => e _ (z j), κ'.symm.injective (κ.injective ?_)⟩
    let ex : Multiplicative (Fin g → ℂ) →* (Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G) :=
      MonoidHom.mk' (fun s => FU.ex i Pe s.toAdd) fun a b => FU.ex_add i Pe hP _ _
    rw [← hv, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp only [Function.comp_def, tie]
    have := map_list_prod ex (List.ofFn fun r : Fin (D.p + D.q) =>
      Multiplicative.ofAdd (F (finSumFinEquiv.symm r) (z (finSumFinEquiv.symm r))))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum,
      Equiv.sum_comp finSumFinEquiv.symm fun j => F j (z j)] at this
    exact this
  · exact (PairingFibre.lamEq_weilEq_over_ring hL _ (T j.isLeft).pol (T j.isLeft).pol B.pol (T j.isLeft).pol
      (Φ j) (Φ j) ((T j.isLeft).t.act.act (Z.hh j)) (𝟙 _) (hΦl j).1 (hΦl j).1 ((T j.isLeft).t.act.hom _)
      inferInstance ℂ σ).1 (hΦp j)
  · have hx' : κ'.symm (e _ z ≫ Φ j) = Over.homMk x hx :=
      κ'.symm_apply_eq.2 (Over.OverMorphism.ext (hxe.symm.trans (hκ' (Over.homMk x hx)).symm))
    rw [← tie, hx', hκ]
    rfl

end GlobalTheory.CM.ExObj
end
end
