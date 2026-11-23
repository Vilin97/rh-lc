module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.StSing
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetryOf
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HeightPullbackDominatingMap
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HodgeCompactPullback
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryTranspositionFactor
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.EmbImmersion
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.ExistsBase
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.PolySmulOfSameSing
public import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement

-- Source module: Development.WeilBound.CoreStatements.JacobiBlockDeterminants.HtCancel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HcptPullK

noncomputable section

namespace HeightCancellation

theorem ht_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' S'' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m : SABMap t' t f)
    (n : SABMap t'' t k) (e : k = g ≫ f) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n


theorem stHt : SquareStatements.StHt := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' _ _ y y' A A' h i j ⟨hdom, hf, hcst, hext, hjo⟩ hR _ hvb
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    infer_instance
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S Ω K J y A hmono
  obtain ⟨x, hx⟩ : ∃ x : Sp Ω ⟶ Xo.XF c, A.ξ ≫ A.f = x ≫ Y.j := ⟨spMap A.fn ≫ x₀, by
    rw [Category.assoc, ← hx₀]
    exact A.fn_over⟩
  have hgen := A.tie.gen
  have hgen' := A'.tie.gen
  obtain ⟨mh, hmh⟩ := ht_cancel A.m A'.m hf
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Ar.LieJ.exists_map A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M hdom mh.cart
  have hjj : ∀ w, j w = j₀ w := fun w => by
    apply A'.M.inj
    apply Over.OverMorphism.ext
    apply A'.m.cart.1.hom_ext
    · refine (hjo w).trans ?_
      show _ = (A'.M.pt (j₀ w)).left ≫ A'.m.φ
      rw [hmh, ← Category.assoc (A'.M.pt (j₀ w)).left, hj₀ w, Category.assoc]
    · rw [Over.w, Over.w]
  have hj : ∀ e, (A'.M.pt (j e)).left ≫ mh.φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap i)) ≫ (A.M.pt e).left :=
    fun e => by rw [hjj e]; exact hj₀ e
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨-, hspan, -⟩ := GlobalTheory.CompanionTheory.Ar.LiePull.main A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M j hgen hgen' hdom
    mh.cart hsm hj
  have hρj : ∀ a e, A'.ρ a (j e) = j (A.ρ a e) := by
    intro a e
    apply A'.M.inj
    rw [A'.act a (j e)]
    apply Over.OverMorphism.ext
    apply mh.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, mh.act a]
      rw [← Category.assoc, hj e, hj (A.ρ a e), A.act a e, Over.comp_left]
      simp only [Category.assoc]
    · rw [Over.w, Over.w]
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li A'.Li j hext hspan
  have hW : ∀ s, eigSp A'.ρ ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li A'.Li j A.ρ A'.ρ (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ A'.X Ω' A'.ξ h i hdom
  have hsp : ∀ p' : Cpt A'.ξ, genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt A'.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt A'.ξ p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt A'.ξ), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt A'.ξ p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt A'.ξ), InFibre A'.ξ p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω' A'.ξ ℤ _ _ A'.tie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt A'.ξ, IsIntegrallyClosed (A'.X.presheaf.stalk q.1) := fun q => (A'.normal q.1).2
  have htors : ∀ p ∈ S, FullTorsion A'.t.G A'.ξ (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ _ hdom mh.cart (A.tors p hp)

  have hω : ∀ p ∈ S, ∀ p' : Cpt A'.ξ, 0 < D.p + D.q → A'.M.htOm A'.t.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt A'.ξ p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A'.X A'.f A'.t A'.m Ω' A'.ξ (spMap i ≫ x) (by
      rw [hf, ← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A'.X Ω' A'.ξ s0' o' A'.t m0' A'.Li A'.M (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := PositivityTheory.UnitarySelfGeneration.height_pullback_dominating_map A.X A'.X Ω Ω' A.ξ A'.ξ h i A.t.G A'.t.G mh.φ A.Li A'.Li A.M A'.M j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq A'.ξ h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  intro p hp s
  have e1 : A'.Vgen s = eigSp A'.ρ ((i.comp A.cst).comp (labelEmb c s)) := by
    rw [← hcst]; rfl
  rw [hR]
  exact GlobalTheory.T.lattice_flag_field_extension A.X A'.X Ω Ω' A.ξ A'.ξ h i A.Li A'.Li j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
    (A'.M.htOm A'.t.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre A'.ξ p q} (labelRk D s) hdom hgen' hext hjd
    (e1.trans (hW s)) (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩

end HeightCancellation
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsMultiHomogRenameBaseInc

section

@[expose] public section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} (blk : σ → Option K)

def baseInc : (Σ k, baseIdx ι blk k) → Σ k, ι k := fun q => ⟨q.1.1, q.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem baseInc_injective : Function.Injective (baseInc (ι := ι) blk) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [baseInc, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl


open Classical in
def extDeg (b : NonPluckerBlocks blk → ℕ) : K → ℕ := fun k => if h : ∀ p, blk p ≠ some k then b ⟨k, h⟩ else 0

theorem isMultiHomog_rename_baseInc {β : MRing (baseIdx ι blk)} {b : NonPluckerBlocks blk → ℕ} (hβ : IsMultiHomog β b) :
    IsMultiHomog (rename (baseInc (ι := ι) blk) β) (extDeg blk b) := by
  classical
  intro m hm k
  rw [support_rename_of_injective (baseInc_injective blk)] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.1 hm
  by_cases h : ∀ p, blk p ≠ some k
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = m₀ ⟨⟨k, h⟩, i⟩ := fun i =>
      Finsupp.mapDomain_apply_of_injective (baseInc_injective blk) m₀ (⟨⟨k, h⟩, i⟩ : Σ k, baseIdx ι blk k)
    simp only [e, extDeg, dif_pos h]
    exact hβ m₀ hm₀ ⟨k, h⟩
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨q, hq⟩
        have : q.1.1 = k := congrArg Sigma.fst hq
        exact h (this ▸ q.1.2))
    simp only [e, extDeg, dif_neg h, Finset.sum_const_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evC_rename_baseInc (z : (Σ k, ι k) → ℂ) (β : MRing (baseIdx ι blk)) :
    Cmp.evC z (rename (baseInc blk) β) = Cmp.evC (basePart blk z) β := by
  simp only [Cmp.evC, map_rename, eval_rename]
  rfl

end SlopeTestRemainingChoices

theorem alg_of : StEmb → StForm → StAlg := by
  intro hE hF E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie n d BM FA hH
  obtain ⟨β, b, hβ, hβn, hβz⟩ := hF E H D l Xo c Y S M.Ω (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐
  have hβ' := isMultiHomog_rename_baseInc M.blk hβ
  refine hE K ι (mCoordIdeal y) (d + 1) _ (FA.S.comap some) (FA.Re.comap some) (rename (baseInc M.blk) β)
    (extDeg M.blk b) FA.J_top FA.deg_one FA.br_empty hβ' ?_ ?_
  · rw [form_mem_mCoordIdeal_iff y hβ', aeval_rename]
    have e : y ∘ baseInc M.blk = algebraMap M.Ω Φ ∘ M.x := funext fun q => M.y_base q
    rw [e, aeval_algebraMap_apply]
    intro h0
    apply hβn
    rw [form_mem_mCoordIdeal_iff M.x hβ]
    exact (algebraMap M.Ω Φ).injective (by rw [h0, map_zero])
  · intro x hx
    have hx' : FA.pr (FA.Re.π x) ∈ ReciprocityTheory.AnForm.P.bdry BM.s := by
      have : FA.S.s (FA.Re.π x) (FA.Re.π x) = 0 := hx
      rw [FA.s_eq] at this
      exact this
    set xb := FA.pr (FA.Re.π x)
    have hmem : BM.Rb.lift xb xb ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem xb xb (BM.Rb.mem_U xb)
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 hmem
    have hnot : ¬ 𝔐.Interior z := fun hI => ((hH.interior xb z hz).2 hI) hx'
    have h0 : Cmp.evC (BM.Rb.lift xb xb) β = 0 := hβz z _ hz hnot
    obtain ⟨c₀, -, hc⟩ := FA.pr_eq x
    show Cmp.evC (FA.Re.R.lift x x) (rename (baseInc M.blk) β) = 0
    rw [evC_rename_baseInc, hc]
    unfold Cmp.evC at h0 ⊢
    rw [eval_smul_homog β b hβ c₀, h0, mul_zero]

end SquareStatements
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.SmoothComb

section

@[expose] public section

noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.StFormB

section

@[expose] public section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

theorem stFormB : StForm := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ x 𝔐
  obtain ⟨hint, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J x 𝔐 RingOfIntegers.coe_injective
  have : IsLocallyNoetherian 𝔐.X := Cmp.HInterior.isLocallyNoetherian_of_coordTie 𝔐.ξ _ 𝔐.tie 𝔐.all
  let U : 𝔐.X.Opens :=
    ⟨abLocus 𝔐.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian 𝔐.t.G 𝔐.t.semi⟩
  have hU : genPt 𝔐.ξ ∈ U := hint
  obtain ⟨β, b, hb, hβ, hw⟩ := Cmp.HInterior.exists_homog_form_point 𝔐.ξ x 𝔐.tie U hU
  refine ⟨β, b, hb, hβ, fun z w hz hnot => ?_⟩
  by_contra hne
  have hmc : w ∈ mcPts (mCoordIdeal x) :=
    ⟨fun k => (hz.1 k).imp fun _ h => h.ne_zero, fun g hg => by
      rw [MvPolynomial.eval_map]
      exact ((tie_points _ _ 𝔐.ξ K J x 𝔐.tie ℂ).2.2 z _ (𝔐.all _) hz).1 g hg⟩
  obtain ⟨z', hz', hzU⟩ := hw w hmc hne
  have e : z = z' := GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J x 𝔐.tie 𝔐.normal 𝔐.all z z' w hz hz'
  subst e
  exact hnot hzU

end SquareStatements
end
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryOfSingularStatement

section

@[expose] public section

namespace SquareStatements

theorem antisymmetry_of_singular_statement (hSing : StSing) : GoodTowerAntisymmetry :=
  good_tower_antisymmetry_of stXB (alg_of stEmb stFormB) HeightCancellation.stHt hSing stBase stCmp
    antisymmetry_transposition_factor

end SquareStatements
end
end

-- Source module: Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem SquareStatements.good_tower_antisymmetry : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  SquareStatements.antisymmetry_of_singular_statement HeightCancellation.stSing
end
end
