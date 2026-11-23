module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.JacobiBlockDeterminants.ExistsColFrame

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HeightCancellation.G

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open SquareStatements.Sing
open scoped ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {r : ℕ}

theorem val_inv {A : Matrix (Fin r) (Fin r) Ω} {h : Matrix (Fin r) (Fin r) ℂ} (hz : genPt ξ ⤳ centre z)
    (hv : ∀ p q, ValAt ξ z (A p q) (h p q)) (hd : h.det ≠ 0) :
    A.det ≠ 0 ∧ ∀ p q, ValAt ξ z (A⁻¹ p q) (h⁻¹ p q) := by
  choose _ s hs hs' using hv
  let S : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s
  let g : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, hz⟩
  let φ : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have e1 : S.map g = A := by ext p q; exact hs p q
  have e2 : S.map φ = h := by ext p q; exact hs' p q
  have hu : IsUnit S.det := CxVal.isUnit (z := z) _ (by
    show φ S.det ≠ 0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, e2]; exact hd)
  have i1 : (S⁻¹).map g * A = 1 := by
    rw [← e1, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have i2 : (S⁻¹).map φ * h = 1 := by
    rw [← e2, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨(Matrix.isUnit_det_of_left_inverse i1).ne_zero, fun p q => ⟨hz, S⁻¹ p q, ?_, ?_⟩⟩
  · rw [Matrix.inv_eq_left_inv i1]; rfl
  · rw [Matrix.inv_eq_left_inv i2]; rfl

theorem val_of_reg {A A' : Matrix (Fin r) (Fin r) Ω} (hξ : IsCptGen ξ) (hz : genPt ξ ⤳ centre z)
    (hA : ∀ p q, A p q ∈ regAt ξ ⟨centre z, hz⟩) (hA' : ∀ p q, A' p q ∈ regAt ξ ⟨centre z, hz⟩) (e : A' * A = 1) :
    ∃ h : Matrix (Fin r) (Fin r) ℂ, h.det ≠ 0 ∧ ∀ p q, ValAt ξ z (A p q) (h p q) := by
  choose s hs using hA
  choose s' hs' using hA'
  let S : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s
  let S' : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of s'
  let g : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, hz⟩
  let φ : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have e1 : S.map g = A := by ext p q; exact hs p q
  have e2 : S'.map g = A' := by ext p q; exact hs' p q
  have e3 : S' * S = 1 := by
    have : (S' * S).map g = (1 : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z))).map g := by
      rw [Matrix.map_mul, e1, e2, e, Matrix.map_one _ (map_zero _) (map_one _)]
    ext p q
    exact hξ.inj ⟨centre z, hz⟩ (congrFun (congrFun this p) q)
  have e4 : S'.map φ * S.map φ = 1 := by
    rw [← Matrix.map_mul, e3, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨S.map φ, (Matrix.isUnit_det_of_left_inverse e4).ne_zero, fun p q => ⟨hz, s p q, hs p q, rfl⟩⟩

end Val

section Lin

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem colFrame_inj {c : Fin r → V} (hc : LinearIndependent Ω c) {A B : Matrix (Fin r) (Fin r) Ω}
    (e : colFrame c A = colFrame c B) : A = B := by
  ext p q
  exact congrFun (GrNorm.coeff_eq_of_li hc (c := fun l => A l q) (d := fun l => B l q) (congrFun e q)) p

theorem colFrame_li {c : Fin r → V} (hc : LinearIndependent Ω c) {A : Matrix (Fin r) (Fin r) Ω} (hA : A.det ≠ 0) :
    LinearIndependent Ω (colFrame c A) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have h1 : ∑ l, (A *ᵥ g) l • c l = ∑ l, (0 : Fin r → Ω) l • c l := by
    rw [show ∑ l, (0 : Fin r → Ω) l • c l = 0 by simp, ← hg]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 := GrNorm.coeff_eq_of_li hc h1
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA h2)

theorem colFrame_mem (A : Subring Ω) {c : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hT : ∀ p q, T p q ∈ A)
    (k : Fin r) : colFrame c T k ∈ Submodule.span A (Set.range c) :=
  Submodule.sum_mem _ fun l _ =>
    (Submodule.span A (Set.range c)).smul_mem (⟨T l k, hT l k⟩ : A) (Submodule.subset_span ⟨l, rfl⟩)

theorem exists_colFrame (A : Subring Ω) {c b : Fin r → V} (h : ∀ k, b k ∈ Submodule.span A (Set.range c)) :
    ∃ T : Matrix (Fin r) (Fin r) Ω, (∀ p q, T p q ∈ A) ∧ b = colFrame c T := by
  choose t ht using fun k => (Submodule.mem_span_range_iff_exists_fun A).1 (h k)
  exact ⟨Matrix.of fun p q => (t q p : Ω), fun p q => (t q p).2, funext fun k => (ht k).symm⟩

theorem step_le {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (s : ℕ) :
    flagStep Ω (colFrame b U) s ≤ flagStep Ω b s := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases h : k < l
  · rw [hU h, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, lt_of_le_of_lt (show (l : ℕ) ≤ k from not_lt.1 h) hk, rfl⟩)

theorem step_eq {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) (s : ℕ) :
    flagStep Ω (colFrame b U) s = flagStep Ω b s := by
  refine le_antisymm (step_le hU s) ?_
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  have h := step_le (b := colFrame b U) (blockTriangular_inv_of_blockTriangular hU) s
  rwa [← colFrame_mul, Matrix.mul_nonsing_inv _ hd.isUnit, colFrame_one] at h

theorem sub_mem_step {b : Fin r → V} {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (k : Fin r) :
    colFrame b U k - U k k • b k ∈ flagStep Ω b k := by
  have e : colFrame b U k - U k k • b k = ∑ l ∈ Finset.univ.erase k, U l k • b l := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    abel
  rw [e]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, h, rfl⟩)
  · rw [hU h, zero_smul]; exact zero_mem _

theorem exists_upper {b b₀ : Fin r → V} (h : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hm : ∀ k : Fin r, b k ∈ flagStep Ω b₀ (k + 1) := fun k =>
    h _ ▸ Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
  choose d hd hd' using fun k => GrNorm.exists_coeff_of_mem_flagStep (hm k)
  exact ⟨Matrix.of fun p q => d q p, fun p q hpq => hd q p hpq, funext hd'⟩

theorem map_colFrame {Ω' V' : Type} [Field Ω'] [AddCommGroup V'] [Module Ω' V'] {i : Ω →+* Ω'} {j : V →+ V'}
    (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) (c : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame c T k)) = colFrame (fun k => j (c k)) (T.map i) := by
  funext k

  simp [colFrame, map_sum, hj]

end Lin

section Frame

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {r : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem frame_change {L : Lat ξ V} (hz : genPt ξ ⤳ centre z) {c : Fin r → V} (hc : L.IsFrameAt c ⟨centre z, hz⟩)
    {A : Matrix (Fin r) (Fin r) Ω} {h : Matrix (Fin r) (Fin r) ℂ} (hv : ∀ p q, ValAt ξ z (A p q) (h p q))
    (hd : h.det ≠ 0) : L.IsFrameAt (colFrame c A) ⟨centre z, hz⟩ := by
  obtain ⟨hA, hi⟩ := val_inv hz hv hd
  have r1 : ∀ p q, A p q ∈ regAt ξ ⟨centre z, hz⟩ := fun p q => let ⟨_, s, hs, _⟩ := hv p q; ⟨s, hs⟩
  have r2 : ∀ p q, A⁻¹ p q ∈ regAt ξ ⟨centre z, hz⟩ := fun p q => let ⟨_, s, hs, _⟩ := hi p q; ⟨s, hs⟩
  refine ⟨colFrame_li hc.1 hA, hc.2.trans (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))⟩
  · rintro _ ⟨k, rfl⟩
    have := colFrame_mem _ (c := colFrame c A) r2 k
    rwa [← colFrame_mul, Matrix.mul_nonsing_inv _ hA.isUnit, colFrame_one] at this
  · rintro _ ⟨k, rfl⟩
    exact colFrame_mem _ r1 k

theorem exists_adapt {L : Lat ξ V} (hξ : IsCptGen ξ) (hz : genPt ξ ⤳ centre z) {c b₀ : Fin r → V}
    (hc : L.IsFrameAt c ⟨centre z, hz⟩) (hb : L.IsFlagVBOn Set.univ b₀) {Q : Matrix (Fin r) (Fin r) Ω}
    (hQ : b₀ = colFrame c Q) : ∃ (U : Matrix (Fin r) (Fin r) Ω) (h : Matrix (Fin r) (Fin r) ℂ),
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ h.det ≠ 0 ∧ ∀ p q, ValAt ξ z ((Q * U) p q) (h p q) := by
  obtain ⟨W, hW, b, hflag, hb'⟩ := hb ⟨centre z, hz⟩ trivial
  have hfr := hb' ⟨centre z, hz⟩ trivial hW
  obtain ⟨U, hU, eU⟩ := exists_upper hflag
  obtain ⟨A, rA, eA⟩ := exists_colFrame (regAt ξ ⟨centre z, hz⟩) (c := c) (b := b) fun k => by
    rw [← hc.2, hfr.2]; exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨A', rA', eA'⟩ := exists_colFrame (regAt ξ ⟨centre z, hz⟩) (c := b) (b := c) fun k => by
    rw [← hfr.2, hc.2]; exact Submodule.subset_span ⟨k, rfl⟩
  have e1 : A' * A = 1 := colFrame_inj hfr.1 (by rw [colFrame_mul, ← eA', ← eA, colFrame_one])
  have e2 : A = Q * U := colFrame_inj hc.1 (by rw [colFrame_mul, ← hQ, ← eU, ← eA])
  obtain ⟨h, hd, hv⟩ := val_of_reg hξ hz rA rA' e1
  refine ⟨U, h, hU, fun h0 => ?_, hd, e2 ▸ hv⟩
  have := (Matrix.isUnit_det_of_left_inverse e1).ne_zero
  rw [e2, Matrix.det_mul, h0, mul_zero] at this
  exact this rfl

end Frame

section Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω']
  {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}

theorem gram_change (A : HodgeCpt Y S x) {z : Spec (CommRingCat.of ℂ) ⟶ A.X} {r : ℕ} {b : Fin r → A.Li}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hG : A.M.GramAt A.t.PP.L z b Γ) {T : Matrix (Fin r) (Fin r) Ω}
    {h : Matrix (Fin r) (Fin r) ℂ} (hv : ∀ p q, ValAt A.ξ z (T p q) (h p q)) :
    A.M.GramAt A.t.PP.L z (colFrame b T) (hᴴ * Γ * h) := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists A.X A.t.G ℂ z
  obtain ⟨v, hv', hΓ⟩ := hG
  choose u hu using fun p => Mz.onto (v p) (GrNorm.tan_of_valAt (hv' p))
  refine ⟨fun q => Mz.pt (∑ p, h p q • u p), fun q => ?_, fun p q => ?_⟩
  · exact HodgeMetric.valAt_sum_smul A.M Mz (A.all _) Finset.univ b u (fun p => by rw [hu]; exact hv' p)
      (fun p => T p q) (fun p => h p q) (fun p => hv p q)
  · exact HodgePull.gram_comb Mz u Γ p (fun p q => by rw [hu, hu]; exact hΓ p q) (HodgePull.hodgeInnerProduct_unique A.m) h p q

theorem gram_pull {A : HodgeCpt Y S x} {A' : HodgeCpt Y S x'} {pr : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}
    (ho : HodgeOver A' A pr i j) {z : Spec (CommRingCat.of ℂ) ⟶ A'.X} {r : ℕ} {b : Fin r → A.Li}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hG : A.M.GramAt A.t.PP.L (z ≫ pr) b Γ) :
    A'.M.GramAt A'.t.PP.L z (fun k => j (b k)) Γ := by
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Ar.Chg.exists_sabMap A A' pr ho.2.1
  have hpt : ∀ e, (A'.M.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap i)) ≫ (A.M.pt e).left := by
    intro e
    have h1 := ho.2.2.2.2 e
    rw [hm] at h1
    refine A.m.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using h1
    · have w1 := Over.w (A'.M.pt (j e))
      have w2 := Over.w (A.M.pt e)
      have w3 : m.φ ≫ A.t.G.hom = A'.t.G.hom ≫ pr := m.cart.1.w
      have hd : A'.ξ ≫ pr = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := ho.1
      rw [Category.assoc, Category.assoc, w3, ← Category.assoc, w1, w2]
      simp only [Over.mk_hom]
      rw [Category.assoc, hd, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      exact congrArg CommRingCat.ofHom (FlagPull.dualMap_algebraMap i).symm
  obtain ⟨v, hv, hΓ⟩ := hG
  have hp : genPt A.ξ ⤳ pr (centre z) := A.all _
  have hL : ∀ k, b k ∈ A.M.lat ⟨pr (centre z), hp⟩ := fun k => by
    obtain ⟨_, u, hu, -⟩ := hv k
    exact Submodule.subset_span ⟨u, hu⟩
  choose w w' hw hw' hww using fun k =>
    HodgePull.value_pull (M' := A'.M) (j := j) ho.1 m.cart hpt (A'.all _) hp (hL k)
  refine ⟨w', hw', fun p q => ?_⟩
  have e : ∀ k, w k = v k := fun k => (hw k).unique A.tie.gen (hv k)
  refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H A'.X A.X A'.t A.t pr m z (w' p) (w' q) (w p) (w q) (hww p) (hww q)).1 _).2 ?_
  rw [e, e]
  exact hΓ p q

theorem grNorm_of (A : HodgeCpt Y S x) {z : Spec (CommRingCat.of ℂ) ⟶ A.X} {r : ℕ} {L : Lat A.ξ A.Li}
    {b b₀ : Fin r → A.Li} (hb : L.IsFrameAt b ⟨centre z, A.all _⟩) {Γ : Matrix (Fin r) (Fin r) ℂ}
    (hG : A.M.GramAt A.t.PP.L z b Γ) (hP : Γ.PosDef) {Q U : Matrix (Fin r) (Fin r) Ω} (hQ : b₀ = colFrame b Q)
    (hU : U.BlockTriangular id) (dU : U.det ≠ 0) {h : Matrix (Fin r) (Fin r) ℂ} (hd : h.det ≠ 0)
    (hv : ∀ p q, ValAt A.ξ z ((Q * U) p q) (h p q)) (k : Fin r) :
    A.M.IsGrNorm A.t.PP.L L b₀ k z (U k k) (grN (hᴴ * Γ * h) k) := by
  have e : colFrame b (Q * U) = colFrame b₀ U := by rw [colFrame_mul, ← hQ]
  refine ⟨A.all _, colFrame b₀ U, hᴴ * Γ * h, step_eq hU dU, e ▸ frame_change _ hb hv hd, sub_mem_step hU k,
    e ▸ gram_change A hG hv, hP.conjTranspose_mul_mul_same ?_, rfl⟩
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit)

end Gram

end HeightCancellation.G
end
end
end

-- Source module: Development.WeilBound.CoreStatements.JacobiBlockDeterminants.DetInvNe

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HeightCancellation.G

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open SquareStatements.Sing
open scoped ComplexOrder

section Blocks

variable {R : Type} [CommRing R] {p q : ℕ}

theorem bmul {A B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hA : IsBlockDiag p A) (hB : IsBlockDiag p B) :
    omBlock (A * B) = omBlock A * omBlock B ∧ wBlock (A * B) = wBlock A * wBlock B := by
  have e := (hA.mul hB).eq_fromBlocks
  rw [← Matrix.submatrix_mul_equiv A B _ (blockEquiv p q) _, hA.eq_fromBlocks, hB.eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  exact ⟨by simpa using e.1.symm, by simpa using e.2.2.2.symm⟩

theorem bd_ct {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) : IsBlockDiag j Aᴴ := fun a b h => by
  rw [Matrix.conjTranspose_apply, hA b a fun e => h e.symm, star_zero]

def blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : Matrix (Fin (p + q)) (Fin (p + q)) R :=
  (Matrix.fromBlocks a 0 0 b).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem blk_apply (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) (s t : Fin q ⊕ Fin p) :
    blk a b (blockEquiv p q s) (blockEquiv p q t) = Matrix.fromBlocks a 0 0 b s t := by
  simp [blk]

theorem om_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : omBlock (blk a b) = a := by
  ext s t; exact blk_apply a b (.inl s) (.inl t)

theorem w_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : wBlock (blk a b) = b := by
  ext s t; exact blk_apply a b (.inr s) (.inr t)

theorem bd_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : IsBlockDiag p (blk a b) := by
  intro s t h
  obtain ⟨s, rfl⟩ := (blockEquiv p q).surjective s
  obtain ⟨t, rfl⟩ := (blockEquiv p q).surjective t
  rw [blk_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact absurd (show (s : ℕ) < p + q - p ↔ (t : ℕ) < p + q - p by omega) h
  · rfl
  · rfl
  · exact absurd (show q + (s : ℕ) < p + q - p ↔ q + (t : ℕ) < p + q - p by omega) h

theorem tri_blk {a : Matrix (Fin q) (Fin q) R} {b : Matrix (Fin p) (Fin p) R} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) : (blk a b).BlockTriangular id := by
  intro s t h
  obtain ⟨s, rfl⟩ := (blockEquiv p q).surjective s
  obtain ⟨t, rfl⟩ := (blockEquiv p q).surjective t
  rw [blk_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact ha (show (t : ℕ) < s from h)
  · rfl
  · rfl
  · exact hb (show (t : ℕ) < s from Nat.lt_of_add_lt_add_left (show q + (t : ℕ) < q + s from h))

end Blocks

section Rev

variable {F : Type} [Field F] {r : ℕ}

theorem tri_rev {U : Matrix (Fin r) (Fin r) F} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) :
    (Uᵀ⁻¹.submatrix Fin.rev Fin.rev).BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  intro a b h
  rw [← Matrix.transpose_nonsing_inv]
  exact blockTriangular_inv_of_blockTriangular hU (show a.rev < b.rev from Fin.rev_lt_rev.2 h)

theorem det_rev (A : Matrix (Fin r) (Fin r) F) : (A.submatrix Fin.rev Fin.rev).det = A.det :=
  Matrix.det_submatrix_equiv_self Fin.revPerm A

theorem det_inv_ne {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : Aᵀ⁻¹.det ≠ 0 :=
  (Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact h.isUnit)).ne_zero

theorem det_col {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : (A.submatrix id Fin.rev).det ≠ 0 := by
  have := Matrix.det_permute' Fin.revPerm A
  refine fun h0 => ?_
  rw [show A.submatrix id Fin.revPerm = A.submatrix id Fin.rev from rfl, h0] at this
  refine mul_ne_zero ?_ h this.symm
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r))) with e | e <;> simp [e]

theorem inv_diag {U : Matrix (Fin r) (Fin r) F} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) (k : Fin r) :
    U⁻¹ k k = (U k k)⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  have hi := blockTriangular_inv_of_blockTriangular hU
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv U hd.isUnit) k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single k] at e
  · exact eq_inv_of_mul_eq_one_right e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hU h, zero_mul]
    · rw [hi h, mul_zero]
  · simp

theorem rev_mul (A B : Matrix (Fin r) (Fin r) F) (f g : Fin r → Fin r) :
    A.submatrix f Fin.rev * B.submatrix Fin.rev g = (A * B).submatrix f g :=
  Matrix.submatrix_mul_equiv A B f Fin.revPerm g

theorem tinv_tinv {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : Aᵀ⁻¹ᵀ⁻¹ = A := by
  rw [← Matrix.transpose_nonsing_inv A, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ h.isUnit]

theorem tinv_mul (A B : Matrix (Fin r) (Fin r) F) : (A * B)ᵀ⁻¹ = Aᵀ⁻¹ * Bᵀ⁻¹ := by
  rw [Matrix.transpose_mul, Matrix.mul_inv_rev]

theorem tinv_rev (A : Matrix (Fin r) (Fin r) F) : (A.submatrix Fin.rev Fin.rev)ᵀ⁻¹ = Aᵀ⁻¹.submatrix Fin.rev Fin.rev :=
  Matrix.inv_submatrix_equiv Aᵀ Fin.revPerm Fin.revPerm

end Rev

section Tot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x} {tie : FlagTie M 𝔐} {𝔐' : HodgeCpt Y S y}
  {Fl : 𝔐'.Flag} {pr : 𝔐'.X ⟶ 𝔐.X} {j : 𝔐.Li →+ 𝔐'.Li} {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk}

theorem mapT (hF : M.IsFrame F) (τ : CMType H) :
    IsBlockDiag D.p ((F.T τ).map (algebraMap M.Ω Φ)) ∧ IsUnit ((F.T τ).map (algebraMap M.Ω Φ)).det := by
  refine ⟨(hF.1 τ).1.map _, ?_⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hF.1 τ).2.isUnit.map _

theorem bdA (hF : M.IsFrame F) (τ : CMType H) : IsBlockDiag D.p (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ) ∧
    (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ).det ≠ 0 := by
  refine ⟨((mapT hF τ).1.inv (mapT hF τ).2).mul (M.g_block τ), ?_⟩
  rw [Matrix.det_mul]
  exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (mapT hF τ).2).ne_zero (M.g_indep.isUnit_det τ).ne_zero

theorem flagW (ht : Tot tie 𝔐' Fl pr j) (hF : M.IsFrame F) (τ : CMType H) :
    Fl.b (.inl τ) = colFrame (fun a => j (tie.wFrame F τ a)) (wBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ)) := by
  funext k
  rw [ht.2.2.1 τ k, FlagTie.wFrame, map_colFrame ht.1.2.2.2.1.1, ← colFrame_mul,
    show (wBlock (F.T τ)).map (algebraMap M.Ω Φ) = wBlock ((F.T τ).map (algebraMap M.Ω Φ)) from rfl,
    ← (bmul (mapT hF τ).1 (bdA hF τ).1).2, Matrix.mul_nonsing_inv_cancel_left _ _ (mapT hF τ).2]

theorem flagO (ht : Tot tie 𝔐' Fl pr j) (hF : M.IsFrame F) (τ : CMType H) {v : Fin D.q → 𝔐.Vgen (.inr τ)}
    (hv : ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0) :
    Fl.b (.inr τ) = colFrame (fun a => j (v a))
      ((omBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ))ᵀ⁻¹.submatrix id Fin.rev) := by
  have hT : (omBlock (F.T τ)).det ≠ 0 := fun h => (hF.1 τ).2 (by rw [(hF.1 τ).1.det_eq_blocks, h, zero_mul])
  have e1 : colFrame (tie.omFrame F τ) (omBlock (F.T τ))⁻¹ = tie.eO τ := by
    rw [FlagTie.omFrame, ← colFrame_mul, Matrix.mul_nonsing_inv _ hT.isUnit, colFrame_one]
  have e2 : (omBlock (F.T τ))⁻¹ᵀ⁻¹ = (omBlock (F.T τ))ᵀ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hT.isUnit]
  have hd := colFrame_dual _ _ hv (omBlock (F.T τ))⁻¹ (Matrix.isUnit_nonsing_inv_det _ hT.isUnit)
  rw [e1, e2] at hd
  have e3 : (fun a => j ((colFrame v (omBlock (F.T τ))ᵀ a : 𝔐.Vgen (.inr τ)) : 𝔐.Li)) =
      colFrame (fun a => j (v a)) (omBlock ((F.T τ).map (algebraMap M.Ω Φ)))ᵀ := by
    refine Eq.trans ?_ (map_colFrame ht.1.2.2.2.1.1 (fun a => (v a : 𝔐.Li)) (omBlock (F.T τ))ᵀ)
    funext a
    simp [colFrame]
  have e4 : omBlock ((F.T τ).map (algebraMap M.Ω Φ)) * omBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ) =
      omBlock (M.g τ) := by
    rw [← (bmul (mapT hF τ).1 (bdA hF τ).1).1, Matrix.mul_nonsing_inv_cancel_left _ _ (mapT hF τ).2]
  have hT' : IsUnit (omBlock ((F.T τ).map (algebraMap M.Ω Φ)))ᵀ.det := by
    have := (mapT hF τ).2
    rw [(mapT hF τ).1.det_eq_blocks] at this
    rw [Matrix.det_transpose]
    exact isUnit_of_mul_isUnit_left this
  funext k
  rw [ht.2.2.2 τ _ hd k, e3, ← colFrame_mul, ← e4, tinv_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hT']
  rfl

theorem frame_up (ht : Tot tie 𝔐' Fl pr j) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X} (s : CMType H ⊕ CMType H) {r : ℕ}
    {b : Fin r → 𝔐.Li} (hb : (𝔐.V s).IsFrameAt b ⟨centre (z ≫ pr), 𝔐.all _⟩) :
    (𝔐'.V s).IsFrameAt (fun a => j (b a)) ⟨centre z, 𝔐'.all _⟩ := by
  rw [ht.2.1 s]
  exact FlagPull.pull_isFrameAt ht.1.1 ht.1.2.2.2.1 ⟨centre z, 𝔐'.all _⟩ (𝔐.all _) hb

end Tot

theorem c3w : GradedLineNormsW := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ B h G ht hF hfr ⟨bB, tB, dB, bh, dh, hv⟩ bG pG _ hG k
  have e : wBlock (hᴴ * G * h) = (wBlock h)ᴴ * wBlock G * wBlock h := by
    rw [(bmul ((bd_ct bh).mul bG) bh).2, (bmul (bd_ct bh) bG).2]; rfl
  rw [e]
  refine grNorm_of 𝔐' (frame_up ht (.inl τ) hfr) (gram_pull ht.1 hG) (pG.submatrix (wEmb_strictMono _ _).injective)
    (flagW ht hF τ) (U := wBlock B) (fun a b hab => tB (wEmb_strictMono _ _ hab))
    (fun h0 => dB (by rw [bB.det_eq_blocks, h0, mul_zero])) (fun h0 => dh (by rw [bh.det_eq_blocks, h0, mul_zero]))
    (fun a b => ?_) k
  rw [← (bmul (bdA hF τ).1 bB).2]
  exact hv _ _

theorem c3o : GradedLineNormsDualOmega := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ B h G ht hF hfr ⟨bB, tB, dB, bh, dh, hv⟩ bG pG
    _ ⟨v, Γ, hv1, hG, hΓ⟩ k
  have dB' : (omBlock B).det ≠ 0 := fun h0 => dB (by rw [bB.det_eq_blocks, h0, zero_mul])
  have dh' : (omBlock h).det ≠ 0 := fun h0 => dh (by rw [bh.det_eq_blocks, h0, zero_mul])
  have tB' : (omBlock B).BlockTriangular id := fun a b hab => tB (omEmb_strictMono _ _ hab)
  have eΓ : Γ = (omBlock G)ᵀ⁻¹ := (Matrix.inv_eq_right_inv hΓ).symm
  have pG' : (omBlock G).PosDef := pG.submatrix (omEmb_strictMono _ _).injective
  have e : revDual (omBlock (hᴴ * G * h)) = ((omBlock h)ᵀ⁻¹.submatrix id Fin.rev)ᴴ * Γ *
      (omBlock h)ᵀ⁻¹.submatrix id Fin.rev := by
    rw [(bmul ((bd_ct bh).mul bG) bh).1, (bmul (bd_ct bh) bG).1, revDual, tinv_mul, tinv_mul, ← eΓ,
      Matrix.conjTranspose_submatrix, Matrix.conjTranspose_nonsing_inv]
    rfl
  have e2 : (B (omEmb D.p D.q k.rev) (omEmb D.p D.q k.rev))⁻¹ = ((omBlock B)ᵀ⁻¹.submatrix Fin.rev Fin.rev) k k := by
    rw [← Matrix.transpose_nonsing_inv]
    exact (inv_diag tB' dB' k.rev).symm
  rw [e, e2]
  refine grNorm_of 𝔐' (frame_up ht (.inr τ) ((omBundle_dualFrame 𝔐 τ _ hfr).2 v hv1)) (gram_pull ht.1 hG)
    (eΓ ▸ pG'.transpose.inv) (flagO ht hF τ hv1) (tri_rev tB' dB') (by rw [det_rev]; exact det_inv_ne dB')
    (det_col (det_inv_ne dh')) (fun a b => ?_) k
  rw [rev_mul, ← tinv_mul, ← (bmul (bdA hF τ).1 bB).1]
  exact (val_inv (A := (omBlock (inFrame M F τ B))ᵀ) (h := (omBlock h)ᵀ) (𝔐'.all _) (fun a b => hv _ _)
    (by rwa [Matrix.det_transpose])).2 a b.rev

theorem c1 : C1 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ ht hF hW hO
  obtain ⟨⟨v, hv⟩, hv'⟩ := omBundle_dualFrame 𝔐 τ _ hO
  obtain ⟨U, h, tU, dU, dh, vU⟩ := exists_adapt 𝔐'.tie.gen (𝔐'.all _) (frame_up ht (.inl τ) hW) (Fl.sub (.inl τ))
    (flagW ht hF τ)
  obtain ⟨U', h', tU', dU', dh', vU'⟩ := exists_adapt 𝔐'.tie.gen (𝔐'.all _) (frame_up ht (.inr τ) (hv' v hv))
    (Fl.sub (.inr τ)) (flagO ht hF τ hv)
  obtain ⟨bA, dA⟩ := bdA hF τ
  set A := ((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ with hA
  have dA' : (omBlock A).det ≠ 0 := fun h0 => dA (by rw [bA.det_eq_blocks, h0, zero_mul])
  have d1 : (h'.submatrix id Fin.rev).det ≠ 0 := det_col dh'
  refine ⟨blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U, blk (h'.submatrix id Fin.rev)ᵀ⁻¹ h, bd_blk _ _,
    tri_blk (tri_rev tU' dU') tU, ?_, bd_blk _ _, ?_, fun a b => ?_⟩
  · rw [(bd_blk _ _).det_eq_blocks, om_blk, w_blk, det_rev]
    exact mul_ne_zero (det_inv_ne dU') dU
  · rw [(bd_blk _ _).det_eq_blocks, om_blk, w_blk]
    exact mul_ne_zero (det_inv_ne d1) dh
  · obtain ⟨a, rfl⟩ := (blockEquiv D.p D.q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv D.p D.q).surjective b
    have e := congrFun (congrFun (bA.mul (bd_blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U)).eq_fromBlocks a) b
    rw [Matrix.submatrix_apply, (bmul bA (bd_blk _ _)).1, (bmul bA (bd_blk _ _)).2, om_blk, w_blk] at e
    rw [blk_apply]
    show ValAt _ _ ((A * blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U) (blockEquiv D.p D.q a) (blockEquiv D.p D.q b)) _
    rw [e]
    have z0 : ValAt 𝔐'.ξ z 0 0 := ⟨𝔐'.all _, 0, map_zero _, map_zero _⟩
    rcases a with a | a <;> rcases b with b | b
    · have e1 : omBlock A * U'ᵀ⁻¹.submatrix Fin.rev Fin.rev =
          (((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev)ᵀ⁻¹ := by
        have e2 : ((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev =
            (omBlock A)ᵀ⁻¹ * U'.submatrix Fin.rev Fin.rev := by
          have e3 : U' = (U'.submatrix Fin.rev id).submatrix Fin.rev id := by
            ext s t; simp
          conv_lhs => rw [e3, rev_mul]
          rfl
        rw [e2, tinv_mul, tinv_tinv dA', tinv_rev]
      rw [e1]
      exact (val_inv (A := (((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev)ᵀ)
        (h := (h'.submatrix id Fin.rev)ᵀ) (𝔐'.all _) (fun a b => vU' _ _) (by rwa [Matrix.det_transpose])).2 a b
    · exact z0
    · exact z0
    · exact vU a b

end HeightCancellation.G
end
end
end
