module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsReindexDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFlagTensor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimes
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefDegreeScaleInvariant
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFreeStatement
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GeoNumOneLin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverPrimesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_comp_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_primes <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLines

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

theorem nefOnFibres_of_wt {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (n : Ψ × Fin N → ℤ)
    (h : ∀ p : ℕ, p.Prime → M.NefAt p (fun τ i => -(n (τ, i) : ℝ)) 0) :
    NefOnFibres (mCoordIdeal M.y) (∑ r, n r • M.xdeg r) := by
  intro W h1 h2 h3 h4
  obtain ⟨d, -, he⟩ := LevelTowerAlt.geoNum_one_lin W
  have h5 := h _ (PB.prime_charOf_of_ne_zero h1.1 h3) W ⟨h1, h2, rfl, h4⟩
  unfold Top.RootModel.curveDeg at h5
  rw [Fintype.sum_option] at h5
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, neg_neg, M.x_deg, he] at h5
  rw [he]
  have : ∑ k, (∑ r, n r • M.xdeg r) k * d k = ∑ r, n r * ∑ k, M.xdeg r k * d k := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [_root_.mul_assoc]
  rw [this]
  exact_mod_cast h5

theorem nefThreshold_of_gap_one {Ψ : Type} [Fintype Ψ] {N j : ℕ} (mu : Top.Wt Ψ N) (b : ℕ) (hb : 4 * Fintype.card Ψ + 2 ≤ b)
    (h1 : ∀ τ i, |mu τ i| ≤ 1) (h2 : ∀ τ, Top.gap j mu τ = 1) : Top.NefThreshold j b mu := by
  intro τ
  have hn : ‖mu‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 τ i
  have hb' : 4 * (Fintype.card Ψ : ℝ) + 2 ≤ b := by exact_mod_cast hb
  rw [h2]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Ψ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.RootNef


theorem _root_.GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  intro hG E _ _ _ H D Xo l c Y S _ M 𝔐 Fl e hY hp hq hS hS' hR
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  have key : ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → (∀ τ i, |mu τ i| ≤ 1) →
      (∀ τ, Top.gap D.p mu τ = 1) → ∀ r : ℕ, r.Prime → M.NefAt r mu 0 := by
    intro mu hd h1 h2 r hr
    by_cases hrS : r ∈ S
    · exact GlobalTheory.T.root_lines_weight_bound_of_free hG.2.2.2.2.2.2.1 E H D l (Xo l) c _ _ Y S M 𝔐 Fl e r hrS (hS r hrS) hR mu hd
    · obtain ⟨a1, a2, a3⟩ := hS' r hr hrS
      exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
        l c hg Y hdom hp hq S M 𝔐 Fl e hR r hr a3 hrS a1 mu hd (GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefThreshold_of_gap_one mu r a2 h1 h2)
  have g1 : D.p - 1 < D.p + D.q := by omega
  have g2 : D.p < D.p + D.q := by omega
  have g3 : ¬ D.p ≤ D.p - 1 := by omega
  have g4 : D.p - 1 < D.p := by omega
  constructor
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if D.p ≤ (r.2 : ℕ) then 1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, one_smul, zero_smul]
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g3]
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if (r.2 : ℕ) < D.p then -1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, neg_smul, one_smul, zero_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g4]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefOnFibresBlockXdegSumsOfRootLinesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | exact GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines | (intros; apply GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSigns

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)


theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  intro hG hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 dg sm m s a e₀ hY hp hq hcov hS hS' hsm hs hdeg
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  obtain ⟨M, 𝔐', Fl, e, i, g, bk, bx, j, hbk, hy, hd, hS2, hR, hj, hli, hV⟩ :=
    GlobalTheory.T.hodge_comp_cover_primes hW E H D Xo l c Y S Ω K J y 𝔐 dg hcov
      (fun p hp hdv => by by_contra h; exact (hS' p hp h).1 hdv) hS
  haveI : CharZero M.Ω := charZero_of_injective_ringHom i.injective
  have hNef : _ ∧ _ :=
    GlobalTheory.T.nefOnFibres_block_xdeg_sums_of_rootLines hG E H D Xo l c Y S M 𝔐' Fl e
      hY hp hq hS2 hS' hR
  obtain ⟨n1, n2⟩ := hNef
  have hb₀ : ∀ σ, LinearIndependent M.Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  have hu := fun τ => GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.det_pull (L := 𝔐.V (sm τ)) hd hj hli (hs τ).1 (hs τ).2 (𝔐.vb (sm τ)) (hb₀ (sm τ))
    (by rw [← hV]; exact Fl.sub (sm τ))
  choose u hu0 hu using hu
  let a' : M.K → ℤ := Function.extend bk a 0
  have ha : ∀ k, a' (bk k) = a k := fun k => hbk.extend_apply _ _ k
  have ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0 := fun k' h => Function.extend_apply' _ _ _ h
  have hB := GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_pull hu0 hd 𝔐.tie.cover hu hbk hy ha ha' hdeg
  simp only [← hV] at hB
  have hgr : ∀ (r : CMType H × Fin (D.p + D.q)) (σ : Σ s, Fin (labelRk D s)), HodgeCpt.rootIdx D r = σ →
      ((𝔐'.V σ.1).gr (Fl.b σ.1) σ.2).IsDegOn Set.univ M.y (HodgeCpt.rootSgn D r • M.xdeg r)
        (e r ^ HodgeCpt.rootSgn D r) := by
    rintro r _ rfl
    refine GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_untens ?_ (hR r)
    unfold HodgeCpt.rootSgn
    split_ifs <;> norm_num
  have hA : ∃ A e₁, (Lat.tens (fun τ => detLat (𝔐'.V (sm τ)) (Fl.b (sm τ))) fun _ => -1).IsDegOn Set.univ M.y A e₁ ∧
      NefOnFibres (mCoordIdeal M.y) A := by
    have hdet : ∀ σ, detLat (𝔐'.V σ) (Fl.b σ) = Lat.tens (fun k => (𝔐'.V σ).gr (Fl.b σ) k) fun _ => 1 := fun σ =>
      GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ σ) (Fl.sub σ)
    simp only [hdet]
    rcases hsm with rfl | rfl
    · have h1 : ∀ τ (k : Fin D.p), HodgeCpt.rootIdx D (τ, Fin.castAdd D.q k) = ⟨.inl τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_left (show ((Fin.castAdd D.q k : Fin _) : ℕ) < D.p from k.2)]
        rfl
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n2 using 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      simp [HodgeCpt.rootSgn]
    · have h1 : ∀ τ (k : Fin D.q), HodgeCpt.rootIdx D (τ, Fin.natAdd D.p k.rev) = ⟨.inr τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_right (by simp)]
        congr 1
        apply Fin.ext
        have := k.2
        simp only [Fin.val_natAdd, Fin.val_rev]
        omega
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n1 using 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      have h2 : ∀ k : Fin D.p, ¬ D.p ≤ (k : ℕ) := fun k => not_le.2 k.2
      have h3 := Equiv.sum_comp Fin.revPerm fun k : Fin D.q => M.xdeg (τ, Fin.natAdd D.p k)
      simp [HodgeCpt.rootSgn, h2, ← h3]
  obtain ⟨A, e₁, hA1, hA2⟩ := hA
  have hN := GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant hI _ M.Ω M.K M.ι M.y 𝔐'.ξ _ A a' e₁ _ _ 𝔐'.tie
    (Finset.prod_ne_zero_iff.2 fun τ _ => hu0 τ) hA1 hB hA2
  obtain ⟨c₀, hc₀⟩ := 𝔐'.tie.cover ⟨genPt 𝔐'.ξ, specializes_rfl⟩
  exact GlobalTheory.T.coords_reindex_degree hI Ω M.Ω i K M.K J M.ι y M.y bk bx a a' hbk hy (fun k => ⟨_, GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.chart_ne hc₀ k⟩) ha ha' hN
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSignsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs | exact GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeUpper

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem span_eq_of_card_nef {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {m r : ℕ} {s : Fin m → V} {b : Fin r → V}
    {U : Submodule Ω V} (hs : LinearIndependent Ω s) (hb : LinearIndependent Ω b)
    (hU : Submodule.span Ω (Set.range b) = U) (hm : ∀ k, s k ∈ U) (h : r = m) :
    Submodule.span Ω (Set.range s) = U := by
  subst hU
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b)) := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hm k
  · rw [finrank_span_eq_card hs, finrank_span_eq_card hb]
    simp [h]

end GlobalTheory.CompanionTheory.Ar.Cusp


theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_upper : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ), admitted Xo l c Y Or B₁ → 4 * Dc.f + 2 ≤ B → NefOnFibres (mCoordIdeal Dc.y) (muTwDeg Hd B) := by
  intro hG hW E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ B hA hB
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨hY, hgood, hS₀, -, hB₁, hS, -⟩ := hA
  obtain ⟨v1, v2, v3, v4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  let g : Cpt Or.𝔐.ξ := ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨ch, hch⟩ := Or.𝔐.tie.cover g
  obtain ⟨m, f, cc, -, -, hsum, hl⟩ := Hd.locally ch hch.1
  have hm : Nonempty (Fin m) := by
    by_contra h0
    rw [not_nonempty_iff] at h0
    simp at hsum
  obtain ⟨bb, -, u, -, hΛ⟩ := hl hm.some
  have hs : ∀ τ k, ∃ s : Or.𝔐.Li, s ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have h1 : Or.i τ (bb τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact LinearMap.mem_range_self _ _
    obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 h1
    exact ⟨z, hz, by rw [← hxz, add_sub_cancel_right]; exact hx⟩
  choose s hs using hs
  obtain ⟨w1, w2⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hspan : ∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = Or.𝔐.Vgen (Or.sm τ) := fun τ => by
    obtain ⟨U, hU, b, hb, hfr⟩ := v4 (Or.sm τ) g trivial
    exact ⟨w1 τ, GlobalTheory.CompanionTheory.Ar.Cusp.span_eq_of_card_nef (w1 τ) (hfr g trivial hU).1 hb (fun k => (hs τ k).1) (Or.rk_sm τ)⟩
  have hj1 := Dc.one_le_j
  have hj2 := Dc.j_le
  have hj3 := Dc.two_le_N
  have hN := Or.N_eq
  have hpq : 1 ≤ D.p ∧ 1 ≤ D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hside : Or.sm = Sum.inl ∨ Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact .inr h
    · exact .inl h
  refine GlobalTheory.T.hodge_comp_cover_cm_signs hG hW E H D Xo l c Y (S₀ ∪ Dc.SB B) Ω K J Dc.y (Or.𝔐.withS _ v1 v2 v3 v4) Or.deg Or.sm _ s _ _
    hY hpq.1 hpq.2 Or.cover (fun p hp => ?_) (fun p hp hpS => ?_) hside hspan w2
  · rcases Finset.mem_union.1 hp with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  · rw [Finset.mem_union, not_or] at hpS
    have h1 : ¬ (p : ℤ) ∣ 2 * discr E * l.M' := fun h => hpS.1 ((hS₀ p).2 ⟨hp, h⟩)
    have h2 : 4 * Dc.f + 2 ≤ p := by
      by_contra h
      exact hpS.2 (Finset.mem_filter.2 ⟨(hS p).2 ⟨hp, by omega, hpS.1⟩, by omega⟩)
    refine ⟨fun h => h1 ((h.mul_left 2).mul_right _), h2, lt_of_le_of_ne hp.two_le ?_⟩
    rintro rfl
    exact h1 ((Dvd.intro _ rfl : ((2 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * discr E).mul_right _)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeUpperStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.intersection_degree_upper : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ), admitted Xo l c Y Or B₁ → 4 * Dc.f + 2 ≤ B → NefOnFibres (mCoordIdeal Dc.y) (muTwDeg Hd B) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_degree_upper | exact GlobalTheory.CompanionTheory.Relay.intersection_degree_upper | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_degree_upper <;> assumption)
end
end
