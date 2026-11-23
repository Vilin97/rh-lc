module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithReciprocityNoCommonDivisorProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomOfChart

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.BcPull

theorem isom_of_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (L M : MLine p σ)
    (e : M.B.ι → L.B.ι) (hU : ∀ a, M.B.U a ≤ L.B.U (e a))
    (hg : ∀ (x : X) a a', x ∈ M.B.U a → x ∈ M.B.U a' →
      gm (𝟙 X) x (M.B.U a ⊓ M.B.U a') (M.B.g a a') = gm (𝟙 X) x (L.B.U (e a) ⊓ L.B.U (e a')) (L.B.g (e a) (e a')))
    (hφ : ∀ a, ∀ y ∈ ptsIn p σ (M.B.U a), M.φ.φ a y = L.φ.φ (e a) y) : L.Isom M := by
  have le (c : M.B.ι × L.B.ι) : M.B.U c.1 ⊓ L.B.U c.2 ≤ L.B.U (e c.1) ⊓ L.B.U c.2 := inf_le_inf_right _ (hU c.1)
  refine ⟨⟨fun c => res (le c) (L.B.g (e c.1) c.2)⟩, fun c c' => Geo.Tor.unit_ext fun x hx => ?_, fun a b y ha hb => ?_⟩
  · have hx' : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ (M.B.U c'.1 ⊓ L.B.U c'.2) := hx
    refine ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c) hx'.1 _)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (Geo.Tor.gm_div L.B M.B (𝟙 X) x c c' hx')
      ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c') hx'.2 _))).trans ?_)
    have h₁ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) (hU _ hx'.2.1) hx'.2.2
    have h₂ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) hx'.1.2 hx'.2.2
    rw [hg x _ _ hx'.1.1 hx'.2.1, mul_right_comm, h₁, ← h₂, mul_inv_cancel_right]
  · rw [hφ a y ha, L.φ.trans (e a) b y (ptsIn_mono (hU a) ha) hb, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact congrArg (fun z : ℂ => _ + Real.log (‖z‖ ^ 2))
      (CxPts.ev_res (le (a, b)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) _).symm

theorem bc_φ {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    {ρ : k →+* K} (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) (i : PUnit → A.B.ι) (z : CxPts q τ) :
    (A.bc w τ).φ.φ i z = A.φ.φ (i PUnit.unit) (bcPt w τ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * A.φ.φ (i a) (bcPt w τ z)).trans (by simp)

theorem bc_pull_isom : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G Z G' : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (w : j ≫ p = q ≫ spMap ρ) (i : Z ⟶ X) (j' : G' ⟶ Z) (g : G' ⟶ G), g ≫ j = j' ≫ i → ∀ (w' : j' ≫ i ≫ p = (g ≫ q) ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)), ((A.pull i rfl).bc w' τ).Isom ((A.bc w τ).pull g rfl) := by
  intro k K _ _ ρ X G Z G' p q j w i j' g h w' τ A
  have hm (a : PUnit → PUnit → A.B.ι) (x : G') (hx : x ∈ ((A.B.pull j).pull g).U a) :
      x ∈ ((A.B.pull i).pull j').U a := by
    have h₀ : j (g x) ∈ A.B.U (a PUnit.unit PUnit.unit) := Geo.Tor.mem_pull.1 (Geo.Tor.mem_pull.1 hx)
    have h₁ : (g ≫ j) x ∈ A.B.U (a PUnit.unit PUnit.unit) := h₀
    rw [h] at h₁
    exact Geo.Tor.mem_pull.2 (Geo.Tor.mem_pull.2 h₁)
  refine isom_of_chart _ _ (fun a : PUnit → PUnit → A.B.ι => a) hm
    (fun x (a a' : PUnit → PUnit → A.B.ι) ha ha' => ?_) fun (a : PUnit → PUnit → A.B.ι) y _ => ?_
  · refine ((Geo.Tor.gm_pull_g (A.B.pull j) g (𝟙 G') x a a' ha ha').trans
      (Geo.Tor.gm_pull_g A.B j (𝟙 G' ≫ g) x _ _ (Geo.Tor.mem_pull.1 ha) (Geo.Tor.mem_pull.1 ha'))).trans (Eq.symm ?_)
    refine ((Geo.Tor.gm_pull_g (A.B.pull i) j' (𝟙 G') x a a' (hm a x ha) (hm a' x ha')).trans
      (Geo.Tor.gm_pull_g A.B i (𝟙 G' ≫ j') x _ _ (Geo.Tor.mem_pull.1 (hm a x ha))
        (Geo.Tor.mem_pull.1 (hm a' x ha')))).trans ?_
    rw [Category.assoc, Category.assoc, h]
  · refine (((A.bc w τ).φ.pull_φ g rfl a y).trans (bc_φ w τ A _ _)).trans (Eq.symm ?_)
    refine ((bc_φ w' τ (A.pull i rfl) a y).trans (A.φ.pull_φ i rfl _ _)).trans (congrArg _ (Subtype.ext ?_))
    change (y.1 ≫ j') ≫ i = (y.1 ≫ g) ≫ j
    rw [Category.assoc, Category.assoc, h]

end GlobalTheory.Mix.BcPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibre

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix



theorem GlobalTheory.Mix.cycInt_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  intro k K _ _ _ _ X G _ p q j hp τ e hX L f x hx
  obtain ⟨hGi, hGn, hGproj, hGdim, hgen, hinj, hstalk, hcoh, hempty⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) hX
  obtain ⟨hZi, hZgen, hZdim, hZuniv⟩ := GlobalTheory.ClosFacts.clos_facts X (j x)
  obtain ⟨hxi, hxgen, -, hxuniv⟩ := GlobalTheory.ClosFacts.clos_facts G x

  have hK : CharZero K := by
    have := hX.charZero_base
    exact (RingHom.charZero_iff (IsFractionRing.injective k K)).1 inferInstance
  have hc : CharZero Γ(clos (j x), ⊤) := by
    obtain ⟨g0, hg0, -, -, -⟩ := hZuniv (clos x) (closι x ≫ j) (by
      simp only [Scheme.Hom.comp_apply, hxgen])
    have : IsDomain Γ(clos x, ⊤) := inferInstance
    let φ : K →+* Γ(clos x, ⊤) :=
      ((closι x ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have : CharZero Γ(clos x, ⊤) := (RingHom.charZero_iff φ.injective).1 hK
    exact g0.appTop.hom.charZero
  have hdim : topologicalKrullDim (clos (j x)) = (e + 1 : ℕ) := by
    rw [hZdim]
    have h1 := (GlobalTheory.MixHt.dimOne k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) (e + 1) hX.dim_eq).1 (j x)
    exact h1.1 ((hcoh x).trans hx)
  have hZ : IsArithVar (closι (j x) ≫ p) e := hX.of_isClosedImmersion (closι (j x)) hc hdim
  haveI := hZi
  let G' := Limits.pullback (closι (j x) ≫ p) (spMap (algebraMap k K))
  let j' : G' ⟶ clos (j x) := Limits.pullback.fst _ _
  let q' : G' ⟶ Sp K := Limits.pullback.snd _ _
  have hp' : IsPullback j' q' (closι (j x) ≫ p) (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hG'i, -, hG'proj, -, hG'gen, -, -, -, -⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K (clos (j x)) G' (closι (j x) ≫ p) q' j' hp' e hZ
  have hw : (j' ≫ closι (j x)) ≫ p = q' ≫ spMap (algebraMap k K) := by
    rw [Category.assoc]; exact hp'.w
  let g : G' ⟶ G := hp.lift (j' ≫ closι (j x)) q' hw
  have hg1 : g ≫ j = j' ≫ closι (j x) := hp.lift_fst _ _ hw
  have hg2 : g ≫ q = q' := hp.lift_snd _ _ hw
  have hp'' : IsPullback j' (g ≫ q) (closι (j x) ≫ p) (spMap (algebraMap k K)) := by rw [hg2]; exact hp'
  have hsq : IsPullback g j' j (closι (j x)) := IsPullback.of_right hp''.flip hg1 hp.flip
  have : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have hgx : g (genericPoint G') = x := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply, hG'gen, hZgen]
  have hproj'' : IsProjOver (g ≫ q) := by rw [hg2]; exact hG'proj
  obtain ⟨-, h1⟩ := GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme K G G' q (g ≫ q) τ hGproj g rfl e (fun i => (L i).bc hp.w τ)
    (fun y => f (bcPt hp.w τ y))
  obtain ⟨-, h2⟩ := GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K (clos (j x)) G' (closι (j x) ≫ p) (g ≫ q) j' hp'' τ e hZ
    (fun i => (L i).pull (closι (j x)) rfl)
  have h3 := fun i => GlobalTheory.Mix.BcPull.bc_pull_isom k K (algebraMap k K) X G (clos (j x)) G' p q j hp.w (closι (j x)) j' g hg1
    hp''.w τ (L i)
  have h4 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver K G' (g ≫ q) τ hproj'' e _ _ h3
  conv_lhs => rw [← hgx]
  rw [h1]
  have h5 := (h2 (fun y => f (ptMap (closι (j x)) rfl _ y))).2
  change _ = Mix.int _ _
  rw [← h5]
  unfold Mix.int
  rw [h4 1, h4 (-1)]
  congr 2 <;> (funext y; exact congrArg f (Subtype.ext (by
    simp only [bcPt_val, PtsOver.map_val, ptMap, Category.assoc, hg1])))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  first | exact @GlobalTheory.Mix.cycInt_genericFibre | exact GlobalTheory.Mix.cycInt_genericFibre | (intros; apply GlobalTheory.Mix.cycInt_genericFibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideEqGenericFibrePullback

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem side_bc_eq : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ e hA Δ Δ' hΔ N L f g
  obtain ⟨_, _, _, _, _, hinj, _, hcoh, hemp⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) hA
  have hcons : (Fin.cons (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) : Fin (e + 1) → MLine q τ) =
      fun i => ((Fin.cons N L : Fin (e + 1) → MLine p (τ.comp (algebraMap k K))) i).bc hp.w τ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have h1 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ (e + 1) hA (Fin.cons N L)).2 f).2
  have hzero : ∀ z : X, z ∉ Set.range j → cycInt L g z = 0 := by
    intro z hz
    haveI := hemp z hz (τ.comp (algebraMap k K))
    simp [cycInt, Mix.int, MeasureTheory.integral_of_isEmpty]
  unfold side
  rw [hcons, h1]
  congr 1
  calc ∑ᶠ x, (Δ'.mult x : ℝ) * cycInt (fun i => (L i).bc hp.w τ) (fun y => g (bcPt hp.w τ y)) x
      = ∑ᶠ x, (Δ.mult (j x) : ℝ) * cycInt L g (j x) := by
        refine finsum_congr fun x => ?_
        rw [hΔ]
        by_cases h : Δ.mult (j x) = 0
        · simp [h]
        · rw [GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre k K X G p q j hp τ e hA L g x
            (by rw [← hcoh]; exact CartierDiv.coheight_eq_one_of_mult_ne_zero h)]
    _ = ∑ᶠ z ∈ Set.range j, (Δ.mult z : ℝ) * cycInt L g z := (finsum_mem_range (f := fun z => (Δ.mult z : ℝ) * cycInt L g z) hinj).symm
    _ = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z := by
        rw [finsum_mem_def]
        refine finsum_congr fun z => ?_
        by_cases hz : z ∈ Set.range j
        · simp [hz]
        · simp [hz, hzero z hz]

end GlobalTheory.Mix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideEqGenericFibrePullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  first | exact @GlobalTheory.Mix.side_bc_eq | exact GlobalTheory.Mix.side_bc_eq | (intros; apply GlobalTheory.Mix.side_bc_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyReciprocityAtComplexEmbedding

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := GlobalTheory.T.arithReciprocity_noCommonDivisor_projective hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyReciprocityAtComplexEmbeddingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.MixRec.side_symm | exact GlobalTheory.MixRec.side_symm | (intros; apply GlobalTheory.MixRec.side_symm <;> assumption)
end
end
