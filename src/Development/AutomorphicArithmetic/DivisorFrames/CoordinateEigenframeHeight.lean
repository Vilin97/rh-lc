import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Cartier
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.GradedNorm GlobalTheory.Mean4O
open scoped ComplexOrder

section SlopeTestRemainingChoices

open GlobalTheory.ShFam.CoordUniq GlobalTheory.ShFam.Pad.Guard

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory in

private theorem indep_v {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (τ : E →+* ℂ) : Indep Z.t x (f.v τ) := by
  intro cf cf' w h1 h2
  refine (f.basis τ w (comb_tan (f.tan τ) h1) fun a => ?_).unique h1 h2
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext (f.eig τ j a)) cf)

private theorem lnStep_change {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X} (f g : EigFrame Z φ x) (p : ℕ)
    {d : Letter Dw → C} (hd : ∀ z, d z ≠ 0)
    (h : ∀ τ i, ∃ cf : Fin (Dw.mult τ) → C, cf i = d ⟨τ, i⟩ ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG Z.t x (f.v τ) cf (g.v τ i)) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    lnStep Z.t x g.v p false st =
      (letterOf Dw st).elim 0 (fun z => Real.log ‖d z‖) + lnStep Z.t x f.v p false st := by
  have hl : lat Z.t p x false = latDR Z.t x := rfl
  rcases st with ⟨τ, k⟩ | k
  · by_cases hk : k < Dw.mult τ
    · simp only [letterOf, lnStep, dif_pos hk, Option.elim, hl]
      rw [grNorm_tri (f.tan τ) (d := fun i => d ⟨τ, i⟩) (fun i => hd _) (h τ), Real.log_mul (norm_ne_zero_iff.2 (hd _))
        (grNorm_latDR_pos Z x (f.tan τ) (indep_v f τ) _).2.ne', add_sub_assoc]
    · simp [letterOf, lnStep, hk]
  · by_cases hk : k < (letters Dw).length
    · obtain ⟨i1, c1⟩ := GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c Z.X Z.t C φ x f.v
        ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩
      have e : letterOf Dw (.inr k) = some ((letters Dw).get ⟨k, hk⟩) := List.getElem?_eq_getElem hk
      simp only [e, lnStep, dif_pos hk, Option.elim, hl]
      rw [grNorm_tri (u := fun i => f.v ((letters Dw).get i).1 ((letters Dw).get i).2) (fun i => f.tan _ _)
        (d := fun i => d ((letters Dw).get i)) (fun i => hd _) (fun j => by
          obtain ⟨cf, e1, e2, e3⟩ := h ((letters Dw).get j).1 ((letters Dw).get j).2
          obtain ⟨cg, a1, a2, a3⟩ := c1 j cf _ e2 e3
          exact ⟨cg, a2.trans e1, a1, a3⟩), Real.log_mul (norm_ne_zero_iff.2 (hd _))
        (grNorm_latDR_pos Z x (fun i => f.tan _ _) i1 _).2.ne']
    · have e : letterOf Dw (.inr k) = none := List.getElem?_eq_none (not_lt.1 hk)
      simp [e, lnStep, hk]

private theorem sum_letters (w : Pad.Sym E →₀ ℤ) (L : Letter Dw → ℝ) :
    ∑ a ∈ w.support, (w a : ℝ) * (letterOf Dw a.2.2).elim 0 L = ∑ z, (expo Dw w z : ℝ) * L z := by
  classical
  simp only [expo, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases letterOf Dw a.2.2 with _ | z
  · simp
  · rw [Finset.sum_eq_single z (fun b _ hb => by simp [hb.symm]) (by simp)]
    simp

private theorem core {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R k C : Type} [CommRing R] [Field k]
    [NontriviallyNormedField C] [IsUltrametricDist C] {φ₂ : c.F →+* R} {x₀ : Sp R ⟶ Z.X} (f₂ : EigFrame Z φ₂ x₀)
    {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (g : EigFrame Z φ x) {ψ : R →+* k} {s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}
    (b₂ : f₂.Tri ψ g s) (J : k →+* C) (χ : R →+* C) (hχ : χ = J.comp ψ) (p : ℕ) (w : Pad.Sym E →₀ ℤ)
    (hw : ∀ a ∈ w.support, a.1 p = false) {r : k} (hr : r ≠ 0) :
    Real.log ‖J r‖ + (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap χ ≫ x₀)
        (fun τ i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap χ) ≫ f₂.v τ i) p (a.1 p) a.2.2) =
      Real.log ‖J (r * ((∏ z : Letter Dw, s z.1 z.2 ^ (-expo Dw w z) : kˣ) : k))‖ +
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap J ≫ x) (fun τ i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap J) ≫ g.v τ i) p false a.2.2 := by
  subst hχ
  have hx : spMap J ≫ x = spMap (J.comp ψ) ≫ x₀ := by
    rw [b₂.1, ← Category.assoc, sp_comp]
  obtain ⟨f', hf'⟩ := f₂.exists_isMap (J.comp ψ) (φ' := J.comp φ) (by rw [b₂.2.1, RingHom.comp_assoc]) hx
  obtain ⟨g', hg'⟩ := g.exists_isMap J rfl rfl
  have key := lnStep_change f' g' p (d := fun z => J (s z.1 z.2))
    (fun z => (map_ne_zero _).2 (Units.ne_zero _)) (fun τ i => by
      obtain ⟨cf, e1, e2, e3⟩ := b₂.2.2 τ i
      refine ⟨fun a => J (cf a), congrArg J e1, fun a ha => (congrArg J (e2 a ha)).trans (map_zero _), ?_⟩
      have := GlobalTheory.LatDRFree.comb_map _ J e3
      simp only [GlobalTheory.GradedPieces.dual_comp] at this
      rw [hg' τ i, funext (hf' τ)]
      exact this)
  have ef : (fun τ i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (J.comp ψ)) ≫ f₂.v τ i) = f'.v :=
    funext fun τ => funext fun i => (hf' τ i).symm
  have eg : (fun τ i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap J) ≫ g.v τ i) = g'.v :=
    funext fun τ => funext fun i => (hg' τ i).symm
  rw [← hx, ef, eg, Finsupp.sum, Finsupp.sum, Finset.sum_congr rfl fun a ha => by rw [hw a ha]]
  simp only [key, mul_add, Finset.sum_add_distrib, sum_letters]
  have hr0 : J r ≠ 0 := (map_ne_zero _).2 hr
  have hs0 (z : Letter Dw) : ‖J (s z.1 z.2)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 (Units.ne_zero _))
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_mul, map_prod, map_zpow₀, norm_mul, norm_prod, norm_zpow]
  rw [Real.log_mul (norm_ne_zero_iff.2 hr0) (Finset.prod_ne_zero_iff.2 fun z _ => zpow_ne_zero _ (hs0 z)),
    Real.log_prod fun z _ => zpow_ne_zero _ (hs0 z)]
  simp only [Real.log_zpow, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

end SlopeTestRemainingChoices

private theorem lg_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (w : Pad.Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) [hp : Fact (resP v).Prime] (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) :
  lgOf Y w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (a.1 (resP v)) a.2.2 := dif_pos hp.out

private theorem pullback_fin_relation {A A' B d lr lb S S' : ℝ} (h0 : A = A') (h1 : A' = d * lr) (h2 : B = d * lb)
    (h3 : lr + S = lb + S') : A + d * S = B + d * S' := by
  rw [h0, h1, h2, ← mul_add, h3, mul_add]
