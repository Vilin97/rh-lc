module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RootIdxLast
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.FieldTheory.Relrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompare
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.HtLabelCongr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

theorem patch_congr' (T : Finset ℕ) (L₀ : Lat ξ V) (Lp Lp' : ℕ → Lat ξ V)
    (h : ∀ p ∈ T, ∀ q, InFibre ξ p q → Lp p q = Lp' p q) : Lat.patch T L₀ Lp = Lat.patch T L₀ Lp' := by
  funext q
  simp only [Lat.patch]
  split_ifs with hF
  · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun hq => ?_
    rw [h p hp q hq]
  · rfl

theorem vbOn_congr {L L' : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {U : Submodule Ω V} (h : ∀ q ∈ T, L q = L' q)
    (hL : L.IsVBOn T r U) : L'.IsVBOn T r U := by
  intro p hp
  obtain ⟨W, hW, b, hb, hf⟩ := hL p hp
  exact ⟨W, hW, b, hb, fun q hq hqW => ⟨(hf q hq hqW).1, (h q hq).symm.trans (hf q hq hqW).2⟩⟩

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem htLabel_congr {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) {n n' : ℕ}
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) {q : Cpt ξ}
    (h : M.htOm L n q = M.htOm L n' q) : htLabel M L n ρ σ s q = htLabel M L n' ρ σ s q := by
  rcases s with τ | τ
  · simp only [htLabel, LieModel.htW, LieModel.htDual, h]
  · simp only [htLabel, LieModel.htDual, h]

section Level

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S₀ y) (S : Finset ℕ)

theorem patch_four (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q)
    (s : CMType H ⊕ CMType H) :
    Lat.patch S (𝔐.dR s) (fun p => htLabel 𝔐.M 𝔐.t.PP.L (p ^ 4) 𝔐.ρ 𝔐.emb s) = 𝔐.VS S s :=
  patch_congr' _ _ _ _ fun p hp q hq => htLabel_congr _ _ _ _ _ (h p hp q hq)

def levFour (hp : ∀ p ∈ S, p.Prime) (hR : ∀ p ∈ S, 4 ≤ 𝔐.R p) (ht : ∀ p ∈ S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p))
    (hvb : ∀ s, (𝔐.VS S s).IsVB (labelRk D s) (𝔐.Vgen s))
    (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q) :
    HodgeCpt Y S y :=
  { 𝔐 with
    S_prime := hp
    R := fun _ => 4
    R_ge := fun _ _ => le_rfl
    tors := fun p hpS k _ i g hg => ht p hpS k i g (by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (hR p hpS)
      rw [hn, pow_add, pow_mul, hg, _root_.one_pow])
    vb := fun s => by
      have h1 := hvb s
      rw [← patch_four 𝔐 S h s] at h1
      exact h1 }

end Level

theorem pull_on {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'} (B : HodgeCpt Y S y) (A : HodgeCpt Y S y') (g : A.X ⟶ B.X)
    (x : Sp Ω ⟶ Xo.XF c) (hx : B.ξ ≫ B.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((B.M.htOm B.t.PP.L (p ^ B.R p)).map (B.Vgen s).dualRestrict).IsVBOn {q | InFibre B.ξ p q}
      (labelRk D s) ⊤)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ B.ξ g i) (hf : g ≫ B.f = A.f) (hR : ∀ p ∈ S, A.R p = B.R p) :
    ∃ (j : B.Li →+ A.Li) (m : SABMap A.t B.t g), IsExtOver i j ∧
      (∀ a, (A.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (B.M.pt a).left) ∧
      ∀ s, A.V s = (B.V s).pull A.ξ g j := by
  obtain ⟨A', e, j', m', p1, p2, p3, p4, p5, p6, p7, -, p9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K K' J J' y y' B x A.X A.ξ g hx hdisc hvb A.all A.tie A.normal hd
  have he : A.ξ ≫ e.symm.hom = A'.ξ := by
    rw [← p1]
    simp
  have hf' : e.symm.hom ≫ A'.f = A.f := by
    rw [p2, ← hf]
    simp
  have hc : A'.cst = A.cst := by
    refine OrLinked.ringHom_ext_int c (OrLinked.spMap_inj' ?_)
    rw [← A'.cst_over, ← A.cst_over, ← hf', ← he]
    simp only [Category.assoc]
  obtain ⟨φ, φt, -, φr, φp⟩ := OrLinked.same_base_cmp A' A e.symm he hf' hc
  have ha : (FrameRebase.sabRebase A.m hf.symm).φ = A.m.φ := FrameRebase.sabRebase_φ _ _
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t B.t A.t B.f g B.m (FrameRebase.sabRebase A.m hf.symm)
  rw [ha] at hk
  let j : B.Li →+ A.Li := φ.toLinearMap.toAddMonoidHom.comp j'
  have hjd : ∀ a, j a = φ (j' a) := fun _ => rfl
  have hj : IsExtOver i j := ⟨fun a v => by rw [hjd, hjd, p6.1, map_smul], fun n b hb =>
    (p6.2 n b hb).map' φ.toLinearMap φ.ker⟩
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ B.ξ (e.hom ≫ g) i := by
    show A'.ξ ≫ e.hom ≫ g = _
    rw [← Category.assoc, p1]
    exact hd
  refine ⟨j, k, hj, fun a => B.m.cart.1.hom_ext ?_ ?_, fun s => ?_⟩
  · show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.m.φ = _
    rw [Category.assoc, ← hk, φt, p3, ← Category.assoc, p7]
  · have w1 := Over.w (A'.M.pt (j' a))
    have w2 := Over.w (A.M.pt (φ (j' a)))
    have w3 : (A'.M.pt (j' a)).left ≫ A'.t.G.hom ≫ e.hom = (A.M.pt (φ (j' a))).left ≫ A.t.G.hom := by
      rw [← Category.assoc, w1, w2, ← p1]
      exact Category.assoc _ _ _
    show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.t.G.hom = _
    rw [← p7, Category.assoc, Category.assoc, k.cart.1.w, m'.cart.1.w, ← Category.assoc, ← w3]
    simp only [Category.assoc]
  · funext q
    obtain ⟨hq, -, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ g i hd q
    obtain ⟨U, hU, b, -, hb⟩ := B.vb s ⟨g q.1, hq⟩ trivial
    have hb1 : (B.V s).IsFrameAt b ⟨g q.1, hq⟩ := hb _ trivial hU
    have h' := OrLinked.genPt_spec e.symm he q
    have e1 : (e.hom ≫ g) (e.symm.hom q.1) = g q.1 := by simp
    have hq' : genPt B.ξ ⤳ (e.hom ≫ g) (e.symm.hom q.1) := e1 ▸ hq
    have hb2 : (B.V s).IsFrameAt b ⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ := by
      have : (⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ : Cpt B.ξ) = ⟨g q.1, hq⟩ := Subtype.ext e1
      rw [this]
      exact hb1
    have hb3 := FlagPull.pull_isFrameAt hd' p6 ⟨e.symm.hom q.1, h'⟩ hq' hb2
    rw [← p9] at hb3
    have hb4 : (A.V s).IsFrameAt (fun k => φ (j' (b k))) q :=
      OrLinked.frame_tr φ (φr q h') (φp S (fun p hp => by rw [p5]; exact hR p hp) s q h') hb3
    exact hb4.2.trans (FlagPull.pull_isFrameAt hd hj q hq hb1).2.symm

end LevelTowerAlt.Comparison₂
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.JoinNormal

section

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (blockFnField)
open PositivityTheory.UnitarySelfGeneration.JN

namespace LevelTowerAlt.Comparison₂

theorem join_normal {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₁ Ω₂ Ω : Type} [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω)
    (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) {X₁ X₂ : Scheme.{0}}
    (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂) (ha₁ : IsArithVar (mCoordIdeal y₁) d)
    (hb₁ : Birational y₁) (hf₁ : FiniteDimensional i₁.fieldRange Ω) (hg₁ : ∀ q : X₁, genPt ξ₁ ⤳ q)
    (hg₂ : ∀ q : X₂, genPt ξ₂ ⤳ q) (ht₁ : CoordTie ℤ ξ₁ fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩)
    (ht₂ : CoordTie ℤ ξ₂ fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, J k)
      (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, J k) (y : (Σ k, J k) → Ω) (Z : Scheme.{0})
      (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧
      (∀ p, y (v₁ p) = i₁ (y₁ p)) ∧ (∀ p, y (v₂ p) = i₂ (y₂ p)) ∧ mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ ∧
      mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧
      CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧
      GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 := by
  obtain ⟨m, w, y, Z, ξ, h₁, h₂, e₁, e₂, -, hg, ht, hN, hd₁, hd₂⟩ :=
    GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join Ω₁ Ω₂ Ω i₁ i₂ K₁ K₂ ι₁ ι₂ y₁ y₂ X₁ X₂ ξ₁ ξ₂ (finite_of i₁ hf₁) hg₁ hg₂ ht₁ ht₂
  let J : K₁ ⊕ K₂ ⊕ Unit → Type := Sum.elim ι₁ (Sum.elim ι₂ fun _ => Fin m)
  have fin : ∀ k, Finite (J k) := by
    rintro (k | k | k)
    · change Finite (ι₁ k); infer_instance
    · change Finite (ι₂ k); infer_instance
    · change Finite (Fin m); infer_instance
  let inst : ∀ k, Fintype (J k) := fun k => Fintype.ofFinite _
  let v₁ : (Σ k, ι₁ k) → Σ k, J k := fun p => ⟨.inl p.1, p.2⟩
  let v₂ : (Σ k, ι₂ k) → Σ k, J k := fun p => ⟨.inr (.inl p.1), p.2⟩
  have hv₁ : IsBlockMap (ι' := J) Sum.inl v₁ := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have hv₂ : IsBlockMap (ι' := J) (fun k => .inr (.inl k)) v₂ := by
    refine ⟨fun _ _ h => Sum.inl_injective (Sum.inr_injective h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have y1 : y ∘ v₁ = fun p => i₁ (y₁ p) := funext fun p => e₁ p.1 p.2
  have y2 : y ∘ v₂ = fun p => i₂ (y₂ p) := funext fun p => e₂ p.1 p.2
  have hb : Birational (ι := J) y := birational_of_tie (ι := J) ht
  obtain ⟨c, hc⟩ := exists_chart (ι := J) ht
  obtain ⟨c₁, hc₁⟩ := exists_chart ht₁
  have F : (blockFnField (ι := J) y).toSubfield = (RingHom.id Ω).fieldRange :=
    blockFnField_eq (ι := J) (RingHom.id Ω) y hb c hc
  have F₁ : (blockFnField (y ∘ v₁)).toSubfield = i₁.fieldRange := by
    rw [y1]; exact blockFnField_eq i₁ y₁ hb₁ c₁ hc₁
  have fd : FiniteDimensional (blockFnField (y ∘ v₁)) Ω := by
    have : FiniteDimensional (blockFnField (y ∘ v₁)).toSubfield Ω := by rw [F₁]; exact hf₁
    exact this
  have I1 : mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ := by rw [y1, mCoordIdeal_map]
  have I2 : mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ := by rw [y2, mCoordIdeal_map]
  refine ⟨K₁ ⊕ K₂ ⊕ Unit, inferInstance, J, inst, Sum.inl, v₁, fun k => .inr (.inl k), v₂, y, Z, ξ, h₁, h₂, hv₁, hv₂,
    congrFun y1, congrFun y2, I1, I2, ?_, hb, hg, ht, hN, hd₁, hd₂, ?_⟩
  · exact GlobalTheory.T.isArithVar_of_block_algebraic K₁ ι₁ _ J Sum.inl v₁ Ω y d hv₁
      (fun k => ⟨c k, Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)⟩) (I1 ▸ ha₁)
      (fun t _ => Algebra.IsAlgebraic.isAlgebraic t)
  · rw [relfinrank_eq i₁ _ _ F₁ F]
    exact Module.finrank_pos.ne'

end LevelTowerAlt.Comparison₂
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullDegSum

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Last

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) [Fintype (CMType H)]

theorem prod_last {M : Type} [CommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∏ r, (if D.p ≤ (r.2 : ℕ) then F r else 1) = ∏ a, F (lastRoot D a) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.prod_eq_one (fun i _ => if_neg (by omega)), one_mul]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.prod_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

theorem sum_last {M : Type} [AddCommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∑ r, (if D.p ≤ (r.2 : ℕ) then F r else 0) = ∑ a, F (lastRoot D a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.sum_eq_zero (fun i _ => if_neg (by omega)), zero_add]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.sum_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

end Last

theorem pullDeg_sum {K K' I : Type} [Fintype I] {κ : K → K'} (hκ : Function.Injective κ) (a : I → K → ℤ) :
    pullDeg κ (∑ j, a j) = ∑ j, pullDeg κ (a j) := by
  funext x
  simp only [pullDeg, Finset.sum_apply]
  by_cases hx : ∃ y, κ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [hκ.extend_apply, Finset.sum_apply]
  · simp only [Function.extend_apply' _ _ _ hx, Pi.zero_apply, Finset.sum_const_zero]


theorem common (h₁ : LevelFree) (h₂ : MuHodge) : Common := by
  intro hG E _ _ _ _ H D Xo l c Y S RM Sys Fx oR II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B hS hdisc hvR hR4 hp hbg hsm hgood hgen
  classical
  subst hS
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := OrLinked.mono_int' c
  have czR : CharZero RM.Ω := charZero_of_injective_ringHom oR.𝔐.cst.injective
  obtain ⟨a1, a2, a3, a4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hfree : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree Or.𝔐 p := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hlev : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ q, InFibre Or.𝔐.ξ p q →
      Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4) q = Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) q := fun p hp' =>
    h₁ hG.2.2.2.2.2.2.1 E H D l (Xo l) c Y _ Ω K J Dc.y (Or.𝔐.withS _ a1 a2 a3 a4) p hp' (by omega) (hfree p hp')
  let B₄ := levFour Or.𝔐 _ a1 a2 a3 a4 hlev
  have hB₄ : ∀ s, B₄.V s = Or.𝔐.VS (S₀ ∪ Dc.SB B) s := patch_four Or.𝔐 _ hlev

  have eg : genPt oR.𝔐.ξ₀ = genPt Or.𝔐.ξ₀ := by
    have g1 := RegAtDom.map_genPt oR.𝔐.fn_over
    have g2 := RegAtDom.map_genPt (show GlobalTheory.CompanionTheory.Ar.Dominates oR.𝔐.ξ Fx.ξf oR.𝔐.f oR.g from oR.g_over)
    rw [hgen, ← g1, g2]
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso oR.𝔐.gen₀ Or.𝔐.gen₀ eg
  have hfin : letI := (Or.𝔐.fn.comp ψ.toRingHom).toAlgebra; Module.Finite oR.𝔐.Ω₀ Ω := by
    have f1 : Or.𝔐.fn.Finite := by
      let _ := Or.𝔐.fn.toAlgebra
      exact Module.finite_of_finrank_pos (Or.cover.2 ▸ Or.cover.1)
    exact RingHom.Finite.comp f1 (RingHom.Finite.of_surjective _ ψ.surjective)
  obtain ⟨Ω₃, _, i₁, i₂, hi, hf₁⟩ := OrLinked.exists_tensor_field oR.𝔐.Ω₀ RM.Ω Ω oR.𝔐.fn _ hfin
  have cz : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have fd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by
    rw [OrLinked.finrank_fieldRange]
    let _ := i₁.toAlgebra
    exact Module.finrank_pos)
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ, v, y, Z, ξ, g₁, g₂, bm₁, bm₂, hy₁, hy₂, I1, I2, har, hbir, hall, htie, hnorm, hd₁, hd₂, hrk⟩ :=
    join_normal i₁ i₂ RM.y Dc.y _ oR.𝔐.ξ Or.𝔐.ξ RM.arith RM.birational fd₁ oR.𝔐.all Or.𝔐.all oR.𝔐.tie Or.𝔐.tie
  obtain ⟨x₁, hx₁'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ RM.Ω RM.K RM.ι RM.y oR.𝔐 hmono
  obtain ⟨x₂, hx₂'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ Ω K J Dc.y Or.𝔐 hmono
  have hx₁ : oR.𝔐.ξ ≫ oR.𝔐.f = (spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    rw [Category.assoc, ← hx₁']; exact oR.𝔐.fn_over
  have hx₂ : Or.𝔐.ξ ≫ Or.𝔐.f = (spMap Or.𝔐.fn ≫ x₂) ≫ Y.j := by
    rw [Category.assoc, ← hx₂']; exact Or.𝔐.fn_over
  have hdisc' : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ Dc.SB B := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨𝔐, a, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, -, q9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 _ Z ξ g₁ hx₁ hdisc'
      (fun p hp s => (hvR p hp).2 s) hall htie hnorm hd₁
  have hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ oR.𝔐.ξ (a.hom ≫ g₁) i₁ := by
    show 𝔐.ξ ≫ a.hom ≫ g₁ = _
    rw [← Category.assoc, q1]
    exact hd₁
  have hdom₂ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ Or.𝔐.ξ (a.hom ≫ g₂) i₂ := by
    show 𝔐.ξ ≫ a.hom ≫ g₂ = _
    rw [← Category.assoc, q1]
    exact hd₂
  have hf𝔐 : 𝔐.f = (a.hom ≫ g₁) ≫ oR.𝔐.f := by rw [q2, Category.assoc]
  obtain ⟨Fl, hbF, -, -, hlF⟩ := FlagPull.flag_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐
    (a.hom ≫ g₁) j₁ m₁ κ₁ v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 fd₁
  have hZ : g₂ ≫ Or.𝔐.f = g₁ ≫ oR.𝔐.f := by
    refine OrLinked.map_eq_of_generic hnorm hall Y.s Y.proj ?_
    have e1 : ξ ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hd₁
    have e2 : ξ ≫ g₂ = spMap i₂ ≫ Or.𝔐.ξ := hd₂
    have e3 : oR.𝔐.ξ ≫ oR.𝔐.f = spMap oR.𝔐.fn ≫ oR.𝔐.ξ₀ := oR.𝔐.fn_over
    have e4 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [← Category.assoc, ← Category.assoc, e1, e2, Category.assoc, Category.assoc, e3, e4, ← hψ, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, OrLinked.spMap_spMap', OrLinked.spMap_spMap', OrLinked.spMap_spMap', hi, RingHom.comp_assoc]
  have hvb₄ : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ s, ((Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4)).map (Or.𝔐.Vgen s).dualRestrict).IsVBOn
      {q | InFibre Or.𝔐.ξ p q} (labelRk D s) ⊤ := fun p hp' s =>
    vbOn_congr (L := (Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p)).map (Or.𝔐.Vgen s).dualRestrict) (fun q hq => by
      simp only [Lat.map]
      rw [hlev p hp' q hq]) ((hfree p hp').2 s)
  have hf₄ : (a.hom ≫ g₂) ≫ Or.𝔐.f = 𝔐.f := by rw [q2, Category.assoc, hZ]
  obtain ⟨j, m, hj, hpt, hV⟩ := pull_on (i := i₂) B₄ 𝔐 (a.hom ≫ g₂) _ hx₂ hdisc'
    hvb₄ hdom₂ hf₄ (fun p hp' => by rw [q5]; exact hR4 p hp')
  have hx : 𝔐.ξ ≫ 𝔐.f = (spMap i₁ ≫ spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    have e1 : 𝔐.ξ ≫ a.hom ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hdom₁
    rw [hf𝔐, ← Category.assoc, e1, Category.assoc, hx₁]
    simp only [Category.assoc]
  obtain ⟨β, d, hβ, hβn, hint⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l (Xo l) c _ _ Y _ Ω₃ K₃ ρ y 𝔐 _ hx hmono
  have hdown : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, ρ k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      CoordsAt Or.𝔐.ξ Dc.y (z ≫ a.hom ≫ g₂) (fun p => w (v p)) ∧ Or.𝔐.Interior (z ≫ a.hom ≫ g₂) := fun z w hw hz =>
    ⟨HodgePull.coordsAt_pull hdom₂ 𝔐.tie.gen Or.𝔐.tie.cover bm₂ hy₂ (𝔐.all _) (Or.𝔐.all _) hw,
      (abLocus_pullback abLocusOne Or.𝔐.t.semi m.cart.1 _).2 hz⟩
  refine ⟨K₃, inferInstance, ρ, inferInstance, κ₁, v₁, κ, v, Ω₃, inferInstance, cz, y, β, d, bm₁, bm₂, I1, I2, har, hβ, hβn,
    hrk, fun w hw hb hBd => ?_, fun L L' hL hL' => ?_⟩
  · obtain ⟨z, hz, hI⟩ := hint w hw hb
    obtain ⟨c1, c2⟩ := hdown z w hz hI
    exact (Or.bd _ _ c1).1 hBd c2
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, lam, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hmet := h₂ hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hn : Dc.N - Dc.j = D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · rw [h, Or.N_eq]; omega
    · rw [hbg] at h
      obtain ⟨τ⟩ : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
      exact absurd (congrFun h τ) (by simp)
  simp only [hsm] at hs hdeg hmet
  choose Lp hLp using fun r => ((GlobalTheory.T.block_pullback_herm_line RM.K RM.ι K₃ ρ κ₁ v₁ bm₁).1 (oR.sing r)).exists
  have hroot : Fl.RootLines (fun r => (Lp r).a) fun r => i₁ (oR.e r) := by
    have h := hlF _ _ oR.lines
    have e : (fun r => (Lp r).a) = fun r => pullDeg κ₁ (RM.xdeg r) := funext fun r => by rw [(hLp r).1, oR.sing_deg]
    rwa [e]
  have hiso := core 𝔐 Fl hbir Lp hroot
    (fun r => HodgePull.hodgeLine_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐 (a.hom ≫ g₁) j₁ m₁ κ₁
      v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 Fl hbF r _ _ _ (oR.hodge r) (hLp r))
    Or.𝔐.t Or.𝔐.tie.gen Or.𝔐.tie.cover Or.𝔐.M (fun τ => Or.𝔐.VS (S₀ ∪ Dc.SB B) (.inr τ)) hdom₂ m j hj hpt
    (fun τ => (hV _).trans (by rw [hB₄]; rfl)) (fun τ => Or.𝔐.Vgen (.inr τ)) (fun τ => a4 (.inr τ)) hn s hsi
    (fun τ k => (hs τ k).1) (muVert Hd B) _ hdeg bm₂ hy₂
    (fun z w hw hz => hmet _ _ (hdown z w hw hz).1 (hdown z w hw hz).2) L L' ?_ (fun w => ?_) hL'
  · obtain ⟨f₁, f₂, hf, hdef⟩ := hiso
    exact ⟨f₁, f₂, hf, fun w hw => hdef w (hint w hw.1 hw.2)⟩
  · rw [hL.1, ← sum_last D fun r => (Lp r).a]
    show pullDeg κ₁ (∑ r, muExp D.p r • (oR.sing r).a) = _
    rw [pullDeg_sum bm₁.1]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [one_smul, (hLp r).1]
    · rw [zero_smul]
      funext k'
      unfold pullDeg
      by_cases h : ∃ k, κ₁ k = k'
      · obtain ⟨k, rfl⟩ := h
        rw [bm₁.1.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ h]
  · rw [hL.2, ← prod_last D fun r => (Lp r).h w]
    show ∏ r, (oR.sing r).h _ ^ muExp D.p r = _
    refine Finset.prod_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [zpow_one, (hLp r).2]
    · rw [zpow_zero]

end LevelTowerAlt.Comparison₂
end
end
end
