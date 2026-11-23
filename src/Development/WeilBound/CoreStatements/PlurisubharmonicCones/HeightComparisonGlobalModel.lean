module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
import all Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLogStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignatureStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspaceStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBoundStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemOfEig
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Monotonicity.Lemmas

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeLogIndex

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had
  obtain ⟨-, -, h3, h4⟩ := LevelTowerAlt.tor_facts A hΨ hv s
  obtain ⟨h5, h6⟩ := LevelTowerAlt.sub_eig A had.2
  have h7 := LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5
  obtain ⟨e1, e2⟩ := LevelTowerAlt.index_split A had.1 h3 h4 hq
  rw [LinPt.fam, e1] at h7
  have h8 := (LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2
  rw [LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]
  ring
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndex

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @LevelTowerAlt.label_degree_log_index | exact LevelTowerAlt.label_degree_log_index
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndexStatement

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.T.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamilyStatement

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.T.log_index_of_orthogonal_family : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | exact GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
  {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ 𝔐.X}
  {P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)} {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V] {MV : LieModel P.tK.G (𝟙 (Sp L)) V} {A : LinPt E L (CMType H) V}

theorem finrank_eig' (h : 𝔐.IsLinPtOf z P MV A) (s : CMType H ⊕ CMType H) :
    Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ trivial
  have h1 := hb _ trivial hU
  have h2 : (𝔐.dR s).IsFrameAt b ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ :=
    ⟨h1.1, (Lat.patch_of_not _ _ _ fun p hp => PtHt.FrameVal.not_inFibre _ _ p (𝔐.S_prime p hp)).symm.trans h1.2⟩
  have hlat := (GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun p hp => PtHt.FrameVal.not_inFibre _ _ p hp)).2.2
  obtain ⟨sL, -, hi, hs⟩ :=
    PtHt.FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 h.1 h.2.1 hlat s b h2
  rw [← hs, finrank_span_eq_card hi, Fintype.card_fin]

omit [∀ k, Fintype (J k)] in
theorem exists_action (h : 𝔐.IsLinPtOf z P MV A) :
    ∃ (t' : SAB H (Sp (𝓞 L))) (_ : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L)))
      (MB : LieModel t'.G (𝟙 _) A.Bq.carrier) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier),
      IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧ MB.IsActOf t'.act.act ρM ∧
        ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x) := by
  obtain ⟨hact, -, -, -, -, t', m', MB, hfib, hl⟩ := h
  obtain ⟨ρM, hρ, -⟩ := lieModel_exists_unique_act _ t'.G (𝓞 L) (𝟙 _) _ MB (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  refine ⟨t', m', MB, ρM, hfib, hρ, fun a x => ?_⟩
  have := t'.semi.separated
  have hinj : Function.Injective (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) := by
    intro u v huv
    have hL := IsFractionRing.injective (𝓞 L) L
    refine TrivSqZeroExt.ext (hL ?_) (hL ?_)
    · simpa [GlobalTheory.CompanionTheory.Ar.dualMap] using congrArg TrivSqZeroExt.fst huv
    · simpa [GlobalTheory.CompanionTheory.Ar.dualMap] using congrArg TrivSqZeroExt.snd huv
  refine MB.inj (Over.OverMorphism.ext (LieHomOk.ext_of_spMap_injective (dualMap (algebraMap (𝓞 L) L))
    hinj t'.G.hom _ _
    ((Over.w (MB.pt _)).trans (Over.w (MB.pt _)).symm) ?_))
  have h1 : (MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl ⟨A.ρ a x, A.stable a x x.2⟩
  have h2 : (MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl x
  have h3 : MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom = (MV.pt x ≫ P.τ.q ≫ P.e.hom) ≫ P.tB.act.act a := by
    rw [hact a x, Category.assoc, P.act a]
    simp only [Category.assoc]
  rw [← h1, h3, hρ a (A.f x)]
  generalize MV.pt x ≫ P.τ.q ≫ P.e.hom = w at h2
  have h4 : (P.tB.act.act a).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
  change (w.left ≫ (P.tB.act.act a).left) ≫ m'.φ =
    spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left ≫ (t'.act.act a).left
  rw [Category.assoc, h4]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (t'.act.act a).left) h2).trans (Category.assoc _ _ _))

end Geo

end LevelTowerAlt
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.HeightComparisonGlobalModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

theorem phiDeg_le_parts {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] {V : Type}
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ)
    (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (X : ℝ)
    (hf : 2 * Fintype.card Ψ = Module.finrank ℚ E) (hO : IsOFamily A.ρ A.I v)
    (hq : ∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ))
    (ha : ∀ τ, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • F τ ≤ A.eig (lab τ) ∧ 𝔞 • A.eig (lab τ) ≤ F τ ∧
      Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ X) :
    A.phiDeg lab F v q ≤ Fintype.card Ψ * (((r : ℝ) + k) * X) - Fintype.card Ψ * (r * Real.log (hostRd E)) +
      ∑ τ, A.Bq.normDegree (A.img (lab τ)) + Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi) := by
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) := ⟨_, rfl⟩
  have hstep : ∀ τ, A.labDeg (lab τ) (F τ) v (q τ) ≤ ((r : ℝ) + k) * X +
      (-(r * Real.log (hostRd E)) + I / Module.finrank ℚ E + A.Bq.normDegree (A.img (lab τ))) := by
    intro τ
    obtain ⟨𝔞, h0, h1, h2, h3⟩ := ha τ
    have hc := GlobalTheory.T.labelled_degree_commensurable_bound E L Ψ V A r k v (lab τ) (q τ) (F τ) 𝔞 (hq τ).1 h0 h1 h2
    have hs := GlobalTheory.T.labelled_degree_eq_log_index E L Ψ V A r k v (lab τ) (q τ) hf hO (hq τ).2 (hq τ).1
    have ht := GlobalTheory.T.log_index_of_orthogonal_family E L Ψ V A r v hf hO (lab τ)
    have h4 : ((r : ℝ) + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ ((r : ℝ) + k) * X := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := (abs_le.1 hc).2
    rw [hs, ht, ← hI] at h5
    unfold hostRd
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun τ _ => hstep τ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hE : (Module.finrank ℚ E : ℝ) = 2 * Fintype.card Ψ := by exact_mod_cast hf.symm
  have hc0 : (Fintype.card Ψ : ℝ) ≠ 0 := by
    have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : Fintype.card Ψ ≠ 0 := by omega
    exact_mod_cast this
  have hcI : (Fintype.card Ψ : ℝ) * (I / Module.finrank ℚ E) = I / 2 := by
    rw [hE]
    field_simp
  have hphi : A.phiDeg lab F v q = ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - I / 2 +
      Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi) := by
    rw [hI]
    rfl
  rw [hphi]
  linarith

theorem small_blocks_numbers {f j r Ca C1 La X rd l4 T : ℝ} (hf : 0 ≤ f) (hj : 0 ≤ j) (hr0 : 0 ≤ r) (hrj : r ≤ j)
    (hLa : 0 ≤ La) (hrd : 0 ≤ rd) (hl4 : l4 ≤ La) (hX : X ≤ (2 * C1 + 2) * La) (hT : T ≤ Ca * (f * j) * La) :
    f * (j * X) - f * (r * rd) + T + f * r / 2 * l4 ≤ (2 * C1 + 2 + Ca + 1) * f * j * La := by
  have hfj : 0 ≤ f * j := mul_nonneg hf hj
  have h1 : f * (j * X) ≤ f * j * ((2 * C1 + 2) * La) := by
    rw [← _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left hX hfj
  have h2 : 0 ≤ f * (r * rd) := mul_nonneg hf (mul_nonneg hr0 hrd)
  have h3 : f * r / 2 * l4 ≤ f * j * La := by
    have h4 : f * r / 2 * l4 ≤ f * r / 2 * La := mul_le_mul_of_nonneg_left hl4 (by positivity)
    have h5 : f * r / 2 * La ≤ f * r * La := by
      have : 0 ≤ f * r * La := by positivity
      nlinarith
    have h6 : f * r * La ≤ f * j * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrj hf) hLa
    linarith
  nlinarith

theorem height_comparison_global_model : (Top.Given → Fl.FlatDegree → FlatSat) → Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
  intro hFS hG hF
  obtain ⟨Cf, hCf0, hflat⟩ := hFS hG hF
  obtain ⟨C1, hC10, hprimes⟩ := GlobalTheory.T.sum_log_prime_div_pred_le_log
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Cs, hCs0, hslope⟩, -⟩ := hG'
  have hC₀ : 0 ≤ Cs + Cf * (2 + C1) := by positivity
  obtain ⟨Ca, hCa0, habel⟩ := abel_abstract (Cs + Cf * (2 + C1)) hC₀
  refine ⟨2 * C1 + 2 + Ca + 1, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ B L _ _ z P V _ _ _ _ MV A r k v q hAdm hB hLin hfin
    hrk hO hq
  obtain ⟨hglob, hgood, hS₀, hcard, -, -, hjj⟩ := hAdm
  obtain ⟨hrd2, hne, hf2⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have hf1 : 1 ≤ Dc.f := Fintype.card_pos_iff.2 hne
  have hN2 := Dc.two_le_N
  have hj1 := Dc.one_le_j
  have hjl := Dc.j_le
  have hj' : Dc.j' = Dc.N - Dc.j := rfl
  have hNeq := Or.N_eq
  have hj'1 : 1 ≤ Dc.j' := by omega
  have hpq : 1 ≤ D.p ∧ 1 ≤ D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hN4 : 4 ≤ Dc.N ^ 2 := by nlinarith
  have hB16 : 16 ≤ B := by nlinarith
  have hfNB : Dc.f * Dc.N ≤ B := by nlinarith [Nat.le_self_pow (n := 2) (by norm_num) Dc.N]
  have hS₀B : S₀.card ≤ B := hcard.trans hB
  obtain ⟨hp, hR, ht, hvb⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hHT : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb) p := by
    intro p hp'
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hLin' : (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb).IsLinPtOf z P MV A := hLin
  have hSr : ∀ r' : ℕ, r'.Prime → (r' : ℤ) ∣ 2 * discr E * l.M' → r' ∈ S₀ ∪ Dc.SB B := fun r' h1 h2 =>
    Finset.mem_union_left _ ((hS₀ r').2 ⟨h1, h2⟩)
  have hSd : ∀ r' : ℕ, r'.Prime → (r' : ℤ) ∣ discr E → r' ∈ S₀ ∪ Dc.SB B := fun r' h1 h2 =>
    hSr r' h1 (Dvd.dvd.mul_right (Dvd.dvd.mul_left h2 2) _)
  have hsumP : ∑ p ∈ S₀ ∪ Dc.SB B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C1 * Real.log B := by
    refine hprimes (S₀ ∪ Dc.SB B) S₀ B (by omega) (fun p hp' => ⟨hp p hp', ?_⟩) hS₀B
    rcases Finset.mem_union.1 hp' with h | h
    · exact _root_.Or.inr h
    · exact _root_.Or.inl (Finset.mem_filter.1 h).2
  have hrd0 : 0 < hostRd E := by linarith
  have hlrd : 0 ≤ Real.log (hostRd E) := Real.log_nonneg (by linarith)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB16' : (16 : ℝ) ≤ B := by exact_mod_cast hB16
  have hLam : abelian₂ B (hostRd E) (hostLval H) = Real.log B + Real.log (hostRd E) + |hostLval H| := by
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂
    rw [Real.log_mul hB0.ne' hrd0.ne']
  have hlogB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  have hLa1 : 1 ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  have hBLa : Real.log B ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  have hl4 : Real.log (4 * Real.pi) ≤ abelian₂ B (hostRd E) (hostLval H) := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hBLa
    linarith [Real.pi_le_four]
  have hexp : ((Fintype.card (CMType H) * (D.p + D.q) : ℕ) : ℝ) ≤ Real.exp (abelian₂ B (hostRd E) (hostLval H)) := by
    have h1 : ((Fintype.card (CMType H) * (D.p + D.q) : ℕ) : ℝ) ≤ B := by
      rw [← hNeq]
      exact_mod_cast hfNB
    have h2 : (B : ℝ) ≤ Real.exp (abelian₂ B (hostRd E) (hostLval H)) := by
      rw [← Real.log_le_iff_le_exp hB0]
      exact hBLa
    exact h1.trans h2
  have hrank : ∀ τ, A.Bq.rank (A.img (Or.sm τ)) ≤ Dc.j' := by
    intro τ
    obtain ⟨k', q', -, -, hk', hrk', -⟩ := (GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hf2).2 r v hO (Or.sm τ)
    have h1 : Module.finrank L (eigSp A.ρ (A.σ (Or.sm τ))) = r + k := by
      rw [← (hq τ).1.2, finrank_span_eq_card (hq τ).1.1, Fintype.card_fin]
    omega
  have hsl : A.Bq.slopeMax ≤ (((Cs + Cf * (2 + C1)) *
      Real.log (2 + Module.finrank (𝓞 L) A.Bq.carrier + max (-A.Bq.normDegree ⊤) 0) : ℝ) : EReal) := by
    obtain ⟨-, -, -, -, hprinc, t', m', MB, hfib, -⟩ := hLin
    refine (hslope E H L t' P.tB m' hprinc A.Bq MB hfib).trans (EReal.coe_le_coe_iff.2 ?_)
    refine mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCf0 (by linarith : (0 : ℝ) ≤ 2 + C1)]) ?_
    refine Real.log_nonneg ?_
    have h1 : (0 : ℝ) ≤ Module.finrank (𝓞 L) A.Bq.carrier := by positivity
    have h2 : (0 : ℝ) ≤ max (-A.Bq.normDegree ⊤) 0 := le_max_right _ _
    linarith
  obtain ⟨t', m', MB, ρM, hfib, hact, hρ⟩ := exists_action Or.𝔐 hLin
  obtain ⟨e1, e2, e3⟩ := eig_facts A ρM hf2 hρ
  obtain ⟨σ₀, -, hσu, -, -, -, hσc⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L
    (spMap (algebraMap (𝓞 L) L) ≫ z)
  have hσ : A.σ = σ₀ := hσu A.σ hLin.2.1
  have hrk2 : ∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) ≤ labelRk D s := by
    intro s
    obtain ⟨k', q', -, -, hk', hrk', -⟩ := (GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hf2).2 r v hO s
    rw [finrank_eig' Or.𝔐 hLin] at hk'
    rw [e1]
    omega
  have hfl0 : ∀ τ, |A.Bq.normDegree (eigSp ρM (intLift (A.σ (.inl τ)))) -
      A.Bq.normDegree (eigSp ρM (intLift (A.σ (.inr τ))))| ≤
      (Cs + Cf * (2 + C1)) * ((D.p + D.q : ℕ) : ℝ) * abelian₂ B (hostRd E) (hostLval H) := by
    intro τ
    have h0 := hflat E H L t' P.tB m' A.Bq MB ρM (intLift (A.σ (.inl τ))) (intLift (A.σ (.inr τ))) hLin.2.2.2.2.1 hfib hact
      (GlobalTheory.T.abelian_part_lie_signature E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L _ P)
      (fun a b hab => A.σ_inj (.inl τ) (congrArg (algebraMap (𝓞 L) L) hab))
      (fun e a => by
        have := DFunLike.congr_fun ((hσc e).2.2 τ) a
        rw [← hσ] at this
        exact this)
    refine h0.trans ?_
    have h2 : 1 + Real.log (hostRd E) + |hostLval H| ≤ (2 + C1) * abelian₂ B (hostRd E) (hostLval H) := by
      have h3 : 0 ≤ C1 * abelian₂ B (hostRd E) (hostLval H) := mul_nonneg hC10 (by linarith)
      have h4 : Real.log (hostRd E) + |hostLval H| ≤ abelian₂ B (hostRd E) (hostLval H) := by
        rw [hLam]
        linarith
      linarith
    have hn : (0 : ℝ) ≤ (D.p : ℝ) + D.q := by positivity
    have hLa0 : 0 ≤ abelian₂ B (hostRd E) (hostLval H) := by linarith
    have h5 : (A.Bq.rank (eigSp ρM (intLift (A.σ (.inl τ)))) : ℝ) + A.Bq.rank (eigSp ρM (intLift (A.σ (.inr τ)))) ≤
        (D.p : ℝ) + D.q := by
      have a1 : A.Bq.rank (eigSp ρM (intLift (A.σ (.inl τ)))) ≤ D.p := hrk2 (.inl τ)
      have a2 : A.Bq.rank (eigSp ρM (intLift (A.σ (.inr τ)))) ≤ D.q := hrk2 (.inr τ)
      exact_mod_cast add_le_add a1 a2
    have h6 : 0 ≤ 1 + Real.log (hostRd E) + |hostLval H| := by positivity
    push_cast
    calc _ ≤ Cf * ((D.p : ℝ) + D.q) * (1 + Real.log (hostRd E) + |hostLval H|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hCf0) h6
      _ ≤ Cf * ((D.p : ℝ) + D.q) * ((2 + C1) * abelian₂ B (hostRd E) (hostLval H)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cf * (2 + C1) * ((D.p : ℝ) + D.q) * abelian₂ B (hostRd E) (hostLval H) := by ring
      _ ≤ (Cs + Cf * (2 + C1)) * ((D.p : ℝ) + D.q) * abelian₂ B (hostRd E) (hostLval H) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hn) hLa0
          linarith
  rw [Fintype.sum_sum_type] at e3
  have hab0 := habel L (CMType H) A.Bq (fun τ => eigSp ρM (intLift (A.σ (Or.sm τ))))
    (fun τ => eigSp ρM (intLift (A.σ (Or.bg τ)))) Dc.j' (D.p + D.q) (abelian₂ B (hostRd E) (hostLval H))
    (Nat.mul_pos hf1 hj'1) hLa1 hexp hfin (fun τ => (e1 _).trans_le (hrank τ)) hsl
    (by
      rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
      · rw [hb, hs]
        linarith
      · rw [hb, hs]
        exact e3)
    (fun τ => by
      rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
      · rw [hb, hs, abs_sub_comm]
        exact hfl0 τ
      · rw [hb, hs]
        exact hfl0 τ)
  have hab := (Finset.sum_le_sum (s := Finset.univ) fun τ _ => e2 (Or.sm τ)).trans hab0
  have hm := GlobalTheory.T.abelian_part_integral_point hG E H D l (Xo l) c Y (S₀ ∪ Dc.SB B) Ω K J Dc.y (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb) L z P V MV A
    (by omega) hSd hHT hLin'
  have hparts := phiDeg_le_parts A Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q
    (2 * (∑ p ∈ S₀ ∪ Dc.SB B, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E)) hf2 hO hq
    fun τ => hm (Or.sm τ)
  have hjr : ((r : ℝ) + k) = Dc.j' := by exact_mod_cast hrk
  have hrj : (r : ℝ) ≤ Dc.j' := by
    rw [← hjr]
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  rw [hjr] at hparts
  refine hparts.trans ?_
  refine small_blocks_numbers (f := Dc.f) (by positivity) (by positivity) (by positivity) hrj (by linarith) hlrd hl4 ?_ hab
  have h3 : C1 * Real.log B ≤ C1 * abelian₂ B (hostRd E) (hostLval H) := mul_le_mul_of_nonneg_left hBLa hC10
  have h4 : Real.log (hostRd E) ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  linarith

end LevelTowerAlt
end
end
