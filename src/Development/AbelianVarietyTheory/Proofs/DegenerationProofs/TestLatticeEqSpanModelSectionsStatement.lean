module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductionsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermuteStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPosIsGreatestNormMulVecOnKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormMulLeOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceIrreducibleResidue

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfPoints

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.LatChar

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩

  rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem mem_span_iff {p : ℕ} [Fact p.Prime] {J A : Type} [Fintype J] [Nonempty J] (B : Matrix J J (PadicAlgCl p))
    (hB : B.det ≠ 0) (T : Set A) (v : A → J → PadicAlgCl p) (κ : ℝ) (hκ : 0 < κ)
    (hle : ∀ a ∈ T, ∀ i, ‖B.mulVec (v a) i‖ ≤ κ)
    (hdet : ∀ c : J → OO p, (∀ a ∈ T, ‖∑ i, (c i : PadicAlgCl p) * B.mulVec (v a) i‖ < κ) →
      ∀ i, ‖(c i : PadicAlgCl p)‖ < 1) (e : J → PadicAlgCl p) :
    e ∈ Submodule.span (OO p) (Set.range B) ↔ ∀ a ∈ T, ‖e ⬝ᵥ v a‖ ≤ κ := by
  have key : ∀ (c : J → PadicAlgCl p) (w : J → PadicAlgCl p),
      (B.vecMul c) ⬝ᵥ w = ∑ i, c i * B.mulVec w i := fun c w => (Matrix.dotProduct_mulVec c B w).symm
  have hvec : ∀ c : J → OO p, ∑ i, c i • B i = B.vecMul fun i => (c i : PadicAlgCl p) := fun c => by
    ext j
    rw [Finset.sum_apply]
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => B i) _).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ a ha
    rw [hvec, key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hκ.le fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 (c i).2)).trans (hle a ha i)
  · intro h
    obtain ⟨c, rfl⟩ : ∃ c, B.vecMul c = e := ⟨B⁻¹.vecMul e, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖c i‖
    by_cases h1 : ‖c i₀‖ ≤ 1
    · exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 ((hi₀ i).trans h1)⟩, hvec _⟩
    exfalso
    rw [not_le] at h1
    have h0 : 0 < ‖c i₀‖ := one_pos.trans h1
    have h0' : c i₀ ≠ 0 := norm_pos_iff.1 h0
    have := hdet (fun i => ⟨c i / c i₀, (mem_OO_iff _).2 (by
      rw [norm_div]; exact (div_le_one h0).2 (hi₀ i))⟩) (fun a ha => by
        have h2 := h a ha
        rw [key] at h2
        have e : ∑ i, c i / c i₀ * B.mulVec (v a) i = (∑ i, c i * B.mulVec (v a) i) / c i₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        show ‖∑ i, c i / c i₀ * B.mulVec (v a) i‖ < κ
        rw [e, norm_div, div_lt_iff₀ h0]
        exact h2.trans_lt (lt_mul_of_one_lt_right hκ h1)) i₀
    simp [div_self h0'] at this

theorem mem_lattice_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)) (κ : ℝ), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → b.det ≠ 0 → 0 < κ → (∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ) → ∀ e : S.J → PadicAlgCl p, e ∈ Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p)))) ↔ ∀ a ∈ l.yy.ker, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ κ := by
  intro L o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b κ hBig hy hL hb hκ hmax e
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre L o Ω S ρ p y₀ u).2.2.2.1, hBig.1, hBig.2.1⟩
  obtain ⟨hN, htor, -⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions L o Ω S ρ p y₀ u l σ cls md hy
  have pb : IsPullback md.r md.Φ.G.hom u.G.hom (rPt p ≫ spMap u.j) := md.cart.1
  have hs : Smooth u.G.hom := md.smooth.smooth
  have : Smooth md.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  refine mem_span_iff _ ?_ (l.yy.ker : Set S.Gam) (fun a i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) κ hκ
    (fun a ha i => (hmax a ha).2 ⟨i, rfl⟩) (fun c hc => ?_) e
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hb
  have hev : ∀ v : S.J → kb p, MvPolynomial.eval v (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) *
      MvPolynomial.X i) = ∑ i, IsLocalRing.residue (OO p) (c i) * v i := fun v => by simp
  have hz := GlobalTheory.T.form_vanishes_of_torsion_torusExtension L.1 L.2.1 (kb p) md.Φ S.g S.N (S.r * S.N) _ S.J _ md.F md.pol hB md.good md.dim hN 1
    (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) * MvPolynomial.X i)
    (Nat.mul_pos (pow_pos (by have := hB.four; omega) _) (Nat.factorial_pos _))
    (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _) ?_
  · have h0 := lin_eq_zero md.Φ md.good (fun i => IsLocalRing.residue (OO p) (c i)) fun v hv =>
      (hev v).symm.trans (hz v hv)
    intro i
    exact (not_isUnit_OO_iff _).1 fun hu => (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu (congrFun h0 i)
  intro x hx
  obtain ⟨a, ha, z, a', hz, hg, hA, hr⟩ := htor x hx
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists md.isLB σ z
  obtain ⟨⟨i₀, -, hi₀⟩, x', hx', hc'⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords L.1 L.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ S.J σ cls
    md hB z w hz hw
  have hxx : x'.left = x.left := pb.hom_ext (hx'.trans hr) ((Over.w x').trans (Over.w x).symm)
  refine ⟨_, hxx ▸ hc', ?_⟩
  have h1 := hL a' _ (hA ▸ (GlobalTheory.T.torsionValues_coords_operator_permute L o Ω S ρ).1 _ y₀ a)
  have h2 := CrdCalc.crd_map (OO p).subtype hw
  rw [show spMap (OO p).subtype ≫ z = u.toG a' from hg] at h2
  obtain ⟨t, ht⟩ := CrdCalc.crd_unique h2 h1
  have hn : κ ≤ ‖(t : PadicAlgCl p)‖ := by
    obtain ⟨i, hi⟩ := (hmax a ha).1
    rw [← hi]
    beta_reduce
    rw [ht i, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 (w i).2)
  have h3 := hc a ha
  have e3 : ∑ i, (c i : PadicAlgCl p) * (b.map (algebraMap _ (PadicAlgCl p))).mulVec
      (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i = t * ((∑ i, c i * w i : OO p) : PadicAlgCl p) := by

    rw [show ((∑ i, c i * w i : OO p) : PadicAlgCl p) = (OO p).subtype (∑ i, c i * w i) from rfl, map_sum,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, map_mul, mul_left_comm]
    rfl
  rw [e3, norm_mul] at h3
  have h4 : ‖((∑ i, c i * w i : OO p) : PadicAlgCl p)‖ < 1 := by
    by_contra h5
    exact absurd h3 (not_lt.2 (hn.trans (le_mul_of_one_le_right (norm_nonneg _) (not_lt.1 h5))))
  rw [hev]
  have h5 : IsLocalRing.residue (OO p) (∑ i, c i * w i) = 0 := by
    by_contra h6
    exact (not_isUnit_OO_iff _).2 h4 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h6)
  simpa using h5

end GlobalTheory.ZH.LatChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH


open TestSpan in
theorem testLattice_eq_span_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l τ σ cls md b hbig hint hmt hlink hdet
  obtain ⟨κ, hκ, hfr⟩ := FrameNorm.exists_pos_isGreatest_norm_mulVec_on_ker hLL o Ω S ρ p y₀ u l σ cls md b hbig hint hlink
  have hΛ := LatChar.mem_lattice_iff hLL o Ω S ρ p y₀ u l σ cls md b κ hbig hint hlink hdet hκ hfr
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  have hE := E_eq_bdd τ φ (fun _ => rfl) (EvCrd.ev_crd_act hLL o Ω S ρ).2
    (GlobalTheory.weightSpace_irreducible_residue hLL o Ω S ρ p φ _ τ.isoFree)
  have hker : ∀ a, a ∈ l.yy.ker ↔ a ∈ τ.yy.ker := fun a => by
    obtain ⟨e, -, he⟩ := hmt
    have h1 := he a 0
    rw [map_zero] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ := τ.δ_max.1
  obtain ⟨i, hi⟩ := (hfr 0 (zero_mem _)).1
  let em := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hy : ∀ a, y₀ a = em (u.yK a) := fun a => (DFunLike.congr_fun u.fac a).symm
  let d : FractionRing u.V := u.yK ⟨S.th x, S.th_mem x⟩
  let k : FractionRing u.V := b.mulVec (fun i => u.yK ⟨S.ev 0 i, S.ev_mem 0 i⟩) i
  have hd : ‖em d‖ = τ.δ := (congrArg norm (hy _)).symm.trans hx
  have hk : ‖em k‖ = κ := by
    refine Eq.trans ?_ hi
    simp only [hy]
    exact congrArg norm (congrFun (map_mulVec' em b _) i).symm
  have hc : ‖em (d / k)‖ = τ.δ / κ := by rw [map_div₀, norm_div, hd, hk]
  have hc0 : em (d / k) ≠ 0 := norm_pos_iff.1 (hc ▸ div_pos τ.δ_pos hκ)
  refine ⟨d / k, fun h => hc0 (by rw [h, map_zero]), ?_⟩
  generalize d / k = c at hc hc0
  let m : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p) :=
    (LinearMap.lsmul (PadicAlgCl p) (S.J → PadicAlgCl p) (em c)).restrictScalars (OO p)
  have hm : ∀ e, m e = em c • e := fun _ => rfl
  have hr : Set.range ((c • b).map em) = m '' Set.range (b.map em) := by
    have h1 : ∀ i, (c • b).map em i = m (b.map em i) := fun i => by
      rw [hm]
      funext j
      simp only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (h1 i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, h1 i⟩
  clear_value m
  rw [hE]
  refine Eq.trans ?_ (congrArg (Submodule.span (OO p)) hr).symm
  rw [Submodule.span_image]
  ext e
  constructor
  · intro he
    refine ⟨(em c)⁻¹ • e, (hΛ _).2 fun a ha => ?_, by rw [hm, smul_inv_smul₀ hc0]⟩
    rw [smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, hc, inv_div, div_mul_eq_mul_div, div_le_iff₀ τ.δ_pos]
    exact mul_le_mul_of_nonneg_left (he a ((hker a).1 ha)) hκ.le
  · rintro ⟨e, he, rfl⟩ a ha
    rw [hm, smul_dotProduct, smul_eq_mul, norm_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hκ]
    exact mul_le_mul_of_nonneg_left ((hΛ _).1 he a ((hker a).2 ha)) τ.δ_pos.le

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSectionsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.testLattice_eq_span_model_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  first | exact @GlobalTheory.ZH.testLattice_eq_span_sections | exact GlobalTheory.ZH.testLattice_eq_span_sections | (intros; apply GlobalTheory.ZH.testLattice_eq_span_sections <;> assumption)
end
end
