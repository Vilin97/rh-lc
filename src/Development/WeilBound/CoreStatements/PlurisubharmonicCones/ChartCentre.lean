module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianFamilyHodgeLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMapStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBoundStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLabelFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamilyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructureStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartHodgeComponentLocalStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSeqCover
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPrincipal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair

theorem weil_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (z : Sp ℂ ⟶ X) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ t.G.left) (g : ℕ) (u : HolUnif A (t.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hpb : IsGrpPullback A t.G z φ) (hAH : u.IsAH Hm χ)
    (tB : SAB H (Sp ℂ)) (m : SABMap tB t z)
    (hP : IsPrincipal tB) (N : ℕ) (ζ : ℂˣ) (a b : Fin g → ℂ) (hN : 0 < N) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ)
    (x y : Over.mk z ⟶ t.G) (hx : x.left = (u.ex ((N : ℂ)⁻¹ • a)).left ≫ φ)
    (hy : y.left = (u.ex ((N : ℂ)⁻¹ • b)).left ≫ φ) (h : CubWeil t.cub N x y (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm *ᵥ star b).im : ℝ) : ℂ) / N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hL' := pull_isLB t.PP.isLB φ
  obtain ⟨ψ, hψ, e₀, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := z)
    (hpb.congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB tB.PP.isLB hL'
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hL'⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  have hak := amplePt _ _ (𝟙 _) _ _ ψ hψ _ _ tB.PP.isLB hL' e₀ hP.2.1 hP.2.2
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hψ
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 hd
      L := t.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpb ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpb fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := hak.1
      ktriv := hak.2 }
  haveI : IsCommMonObj A := hA.comm
  have tors : ∀ w : Fin g → ℂ, w ∈ u.Λ → u.ex ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul_hol, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (u.ker w).2 hw
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf hpb) t.PP t.cub
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil c' (tors a ha) (tors b hb)
  have hw' : (cubeMapOf hpb).F ≫ t.G.hom = A.hom ≫ z := hpb.1.w
  have mul : ∀ (T : Over (Sp ℂ)) (p q : T ⟶ A), Out.toBase hw' (p * q) = Out.toBase hw' p * Out.toBase hw' q :=
    fun T p q => Over.OverMorphism.ext (hpb.2 T p q _ _ rfl rfl).symm
  have h1 := cubWeil_of_isPullCubical _ _ z t.G A (cubeMapOf hpb) hw' mul _ _ t.cub c' hc N _ _ _ ξ hξ
  have h2 : CubWeil t.cub N x y ξ := cubWeil_congr (Category.id_comp z) hx hy h1
  obtain rfl : ξ = unitOn ζ := h2.unique h
  have hW₁ : Out.WeilIs Q.A Q.L N (u.ex ((N : ℂ)⁻¹ • a)) (u.ex ((N : ℂ)⁻¹ • b)) (unitOn ζ) :=
    (cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA (tors a ha) (tors b hb) _).1 hξ
  obtain ⟨Ef, hE, -, -, -, -, hWe⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (Ef ⟨a, ha⟩ ⟨b, hb⟩ : ℂ) / N)) (Complex.exp_ne_zero _)
  have hW₂ := hWe N ⟨a, ha⟩ ⟨b, hb⟩ c hN rfl
  have e := ((GlobalTheory.abelianSchemeLaws_all.1.weil (Sp ℂ) Q N (𝟙_ _)).1 _ _ (tors a ha) (tors b hb)).unique hW₁ hW₂
  have e' : ζ = c := Units.ext (by
    have := congrArg (fun v : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v.val) e
    simpa [unitOn] using this)
  rw [e']
  show Complex.exp _ = _
  have i := hE ⟨a, ha⟩ ⟨b, hb⟩
  congr 3
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) i

theorem cubWeil_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {Z : Scheme.{0}} (a : Z ⟶ S') {N : ℕ}
    {x y : Over.mk a ⟶ t'.G} {x₀ y₀ : Over.mk (a ≫ f) ⟶ t.G} (ex : x₀.left = x.left ≫ m.φ)
    (ey : y₀.left = y.left ≫ m.φ) {ζ : Γ(Z, ⊤)ˣ} (h : CubWeil t'.cub N x y ζ) : CubWeil t.cub N x₀ y₀ ζ := by
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y _ _ rfl rfl).symm
  have h1 := GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin N (Over.mk a) x y ζ h
  exact cubWeil_congr rfl ex ey h1

theorem exists_principal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a) {X : Scheme.{0}} {t : SAB H X}
    {jj : Sp C.R ⟶ X} (m : SABMap C.t t jj) {b : Fin n → ℂ} (hb : b ∈ Flat.punct n a 1) :
    ∃ (tB : SAB H (Sp ℂ)) (_ : SABMap tB t (spMap (C.ψ b) ≫ jj)), IsPrincipal tB := by
  obtain ⟨t', ⟨m₀⟩⟩ := exists_sab (C.pt b) C.tV
  obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
  obtain ⟨mX, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mK
  obtain ⟨w₂, g₂, -⟩ := mx.lin
  obtain ⟨am, kt⟩ := amplePt _ _ _ _ _ mx.φ mx.cart _ _ Xo.univ.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Xo.univ.ample
    Xo.univ.ktriv
  rw [(C.pt_eq b hb).1] at mX
  exact ⟨t', mX, MorphismProperty.of_isPullback (P := @IsProper) mx.cart.1 Xo.univ.proper, am, kt⟩

end LevelTowerAlt.Val
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.ChartCentre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem chart_centre (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts) (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)
    (ht₀ : t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1)) (z₀ : Sp ℂ ⟶ Or.𝔐.X) (hz₀ : CoordsAt Or.𝔐.ξ Dc.y z₀ ((Dc.chart a).γ t₀))
    (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (hsm : Or.IsSmallPart d s)
    (ν : ℝ) (hν : Or.𝔐.GeoPhi Or.sm z₀ s ν) :
    ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) ∧
      ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ‖GroundTheory.Heights₂.Heights.Regular.expCover a₀ w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) -
            Real.log ((L.riem w hw).nz σ I) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpq : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  have hfr := (((GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀).2 d).2 s hsm).1
  have hval0 : ∀ i : CMType H × Fin (Dc.N - Dc.j), ∃ v : epsAt z₀ ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt z₀ (s i.1 i.2) v := fun i =>
    GlobalTheory.T.hodge_component_label_frame E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z₀ (Or.sm i.1) _ (s i.1) (Or.𝔐.all _) (hfr i.1 _) i.2
  obtain ⟨a₀, π, ρ₁, σ₀, C, jj, m, sc, hρ₁, hA⟩ := GlobalTheory.T.snc_chart_hodge_component_local hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 _ Dc.Bd (Dc.chart a) t₀
    d.c d.f (CMType H × Fin (Dc.N - Dc.j)) (fun i => s i.1 i.2) z₀ Or.bd ht₀ hz₀ d.inDom hval0
  obtain ⟨ρ₂, Λ, _, L₀, e, hρ₂, hρ₂1, hper, hRiem⟩ := GlobalTheory.T.boundary_chart_log_period_family E H D l (Xo l) σ₀ _ a₀ C hpq
  obtain ⟨Bf, hBd, hBe⟩ := GlobalTheory.T.holomorphic_endomorphism_family E H C.R C.t C.g _ C.M ρ₂ C.ψ e hρ₂
  have hnorm : ∀ u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ, ‖(ρ₂ : ℂ) • u‖ = ρ₂ * ‖u‖ := fun u => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ₂.le]
  have hsmρ : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ρ₂ := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [hnorm]
    nlinarith
  have hsm1 : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := fun u hu =>
    Metric.ball_subset_ball hρ₂1 (hsmρ u hu)
  have hsmd : DifferentiableOn ℂ (fun u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ => (ρ₂ : ℂ) • u)
      (Metric.ball 0 1) := (differentiable_id.fun_const_smul _).differentiableOn
  have hBhol : ∀ c x, DifferentiableOn ℂ (fun z => Bf ((ρ₂ : ℂ) • z) c x) (Metric.ball 0 1) := fun c x =>
    (hBd c x).comp hsmd hsmρ
  have hpb : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le,
      GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := fun w hw => ChartFree.expCover_mem_punct L₀.a_le hw
  have hclosed : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, ∀ c x, ∃ y, L₀.P w y =
      Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) c (L₀.P w x) := by
    intro w hw c x
    have hb := hsmρ _ (hpb w hw).1
    have h1 : e.ex _ (L₀.P w x) = 1 := ((hper w hw _).2 ⟨x, rfl⟩ : _)
    refine (hper w hw _).1 ?_
    show e.ex _ _ = 1
    rw [hBe _ hb, h1]
    haveI := C.t.act.hom c
    simp
  obtain ⟨instM, hact⟩ := GlobalTheory.T.log_periods_module_structure E _ a₀ C.g Λ L₀ (fun z => Bf ((ρ₂ : ℂ) • z)) hBhol hclosed
  have hInt : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ u ∈ Flat.punct _ a₀ 1) := by
    intro u hu
    obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 u hu)
    have h5 := Or.bd _ _ h3
    have h6 : Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ (ρ₂ : ℂ) • u ∈ Flat.punct _ a₀ 1 := by
      rw [← h4, h5, not_not]
    rw [h6]
    have hne : (ρ₂ : ℂ) ≠ 0 := by exact_mod_cast hρ₂.ne'
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hu, fun i hi h0 => h i hi (by simp [h0])⟩
    · rintro ⟨-, h⟩
      exact ⟨hsm1 u hu, fun i hi => by simpa [hne] using h i hi⟩
  have hF : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, _ := fun w hw =>
    GlobalTheory.T.boundary_chart_hodge_map hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 σ₀ _ a₀ C jj m (Metric.ball 0 ρ₂) e
      ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) (Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w))
      (L₀.H (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) hpq (hsmρ _ (hpb w hw).1)
      ((hInt _ (hpb w hw).1).2 (hpb w hw)) (hRiem _ (hpb w hw)) (hBe _ (hsmρ _ (hpb w hw).1))
  have hinj : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, Function.Injective (L₀.P w) := by
    intro w hw
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine L₀.unimod.1 ?_
    ext y
    have h := L₀.im w hw x y
    rw [hx] at h
    simpa using h.symm
  have hw₀ : ∃ w₀, w₀ ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le := by
    refine ⟨fun k => if (k : ℕ) < a₀ then -1 else 0, fun i => ?_, fun k hk => ?_⟩
    · simp
    · simp [not_lt.2 hk]
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hadj : ∀ c c' : 𝓞 E, (c' : E) = IsCMField.complexConj E (c : E) → ∀ x y, L₀.E (c • x) y = L₀.E x (c' • y) := by
    intro c c' hc x y
    obtain ⟨A, _, φ, u, χ', -, -, -, -, -, h⟩ := hF w₀ hw₀
    have h1 := L₀.im w₀ hw₀ (c • x) y
    have h2 := L₀.im w₀ hw₀ x (c' • y)
    rw [hact w₀ hw₀] at h1
    rw [hact w₀ hw₀] at h2
    have h3 := h c c' hc (L₀.P w₀ x) (L₀.P w₀ y)
    have h4 : ((L₀.E (c • x) y : ℤ) : ℝ) = ((L₀.E x (c' • y) : ℤ) : ℝ) := by
      rw [← h1, ← h2]
      exact congrArg Complex.im h3
    exact_mod_cast h4
  let L : ActPeriods E _ a₀ C.g Λ :=
    { toLogPeriods := L₀
      adj := hadj
      B := fun z => Bf ((ρ₂ : ℂ) • z)
      B_hol := hBhol
      act := hact }
  obtain ⟨σa, hσ, hinl, hinr⟩ := GlobalTheory.T.holomorphic_points_of_component E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R jj _ C.ψ C.hol
  have hcm : IsCMFam (fun τ => σa (Or.sm τ)) := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h]
    · exact hinr
    · exact hinl
  have hdiffb : ∀ (r : C.R), DifferentiableOn ℂ (fun u => C.ψ ((ρ₂ : ℂ) • u) r) (Metric.ball 0 1) := fun r =>
    (C.hol.2 r).comp hsmd hsm1
  have hframe : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∀ τ
      (h : genPt Or.𝔐.ξ ⤳ centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj)),
      (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj), h⟩ := by
    intro u hu τ h
    obtain ⟨-, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    have h4 := (GlobalTheory.T.component_data_intersection_bound hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ h3).2 { d with inDom := h2 }
    exact (h4.2 s hsm).1 τ h
  have hEig : IsEigFrames (Metric.ball 0 1) L.B (fun τ => σa (Or.sm τ))
      (fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i)) := by
    refine ⟨fun τ k => differentiableOn_pi.2 fun i => hdiffb _, fun t ht τ => ?_⟩
    exact GlobalTheory.T.abelian_family_hodge_lattice E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R C.t jj m C.g _ C.M (Metric.ball 0 ρ₂) C.ψ e ((ρ₂ : ℂ) • t)
      (Bf ((ρ₂ : ℂ) • t)) (Or.sm τ) _ (s τ) (fun k => sc (τ, k)) σa (hsmρ t ht) (hBe _ (hsmρ t ht))
      (hσ _ (hsm1 t ht)) (hframe t ht τ) (fun k => (hA _ (hsm1 t ht)).2.2.2.2 (τ, k))
  refine ⟨a₀, C.g, Λ, inferInstance, instM, L, π, ρ₁ * ρ₂, fun τ => σa (Or.sm τ),
    fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj, fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i),
    mul_pos hρ₁ hρ₂, hcm, hEig, fun u hu => ?_, fun w hw => ?_, ?_⟩
  · have heq : t₀ + (((ρ₁ * ρ₂ : ℝ)) : ℂ) • (u ∘ π) = t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • u) ∘ π) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      push_cast
      ring
    rw [heq]
    obtain ⟨h1, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    exact ⟨h1, h2, h3, fun i a' => hσ _ (hsm1 u hu) (Or.sm i) a', hInt u hu⟩
  · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, hdv, -⟩ := hF w hw
    have hbρ := hsmρ _ (hpb w hw).1
    choose v hv1 hv2 using (hA _ (hsm1 _ (hpb w hw).1)).2.2.2.2
    refine ⟨v, fun i => hv1 i, ?_⟩
    refine ⟨A, instA, φ, u, χ', hgp, hAH, fun a' p => ?_, hinj w hw, fun p => ?_, fun i => ?_⟩
    · show (u.ex (Bf _ a' p)).left ≫ φ = _
      have e1 : (u.ex p).left ≫ φ ≫ (Or.𝔐.t.act.act a').left = ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ (Or.𝔐.t.act.act a').left := by
        rw [← hex p, Category.assoc]
      rw [hex, e1, hBe _ hbρ, Over.comp_left, Category.assoc, Category.assoc, m.act]
    · rw [hlat p]
      exact hper w hw p
    · obtain ⟨v', h1, h2⟩ := hdv _ _ (Flat.FrameDeriv.isDerivAt0_pt e hbρ (sc i))
      exact ⟨v', by rw [h1, hv2 i, Category.assoc], h2⟩

  · have h0 : (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := Metric.mem_ball_self one_pos
    obtain ⟨-, -, co0, -, hv0⟩ := hA _ (hsm1 0 h0)
    have hT0 : t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)) ∘ π) = t₀ := by
      funext i; simp
    rw [hT0] at co0
    have hz : z₀ = spMap (C.ψ ((ρ₂ : ℂ) • 0)) ≫ jj :=
      GlobalTheory.T.normal_scheme_coords_injective _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie Or.𝔐.normal Or.𝔐.all _ _ _ hz₀ co0
    rw [hz] at hν
    obtain ⟨P, V, _, _, MV, ρV, I₀, hf, σ', bz, g1, g2, g3, g4, g5, g6⟩ := hν
    have hσ' : σ' = fun τ => σa (Or.sm τ) := funext fun τ => RingHom.ext fun a' =>
      WeightSheet.valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (g3 τ a') (hσ _ (hsm1 0 h0) (Or.sm τ) a')
    rw [hσ'] at g6
    refine centre_phi C m hρ₂ hρ₂1 e L (fun w hw => ⟨hper w hw, fun N ζ x x' hN hc => ?_⟩) (hBe _ (hsmρ 0 h0)) _ _
      (fun τ k => sc (τ, k)) (fun _ _ => rfl) hcm hEig P MV ρV I₀ hf g1 g2 g4 bz (fun τ k => ?_) g6
    · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, -, -⟩ := hF w hw
      have hpp : (ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := by
        obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 _ (hpb w hw).1)
        exact h4.1 fun hb => (Or.bd _ _ h3).1 hb ((hInt _ (hpb w hw).1).2 (hpb w hw))
      obtain ⟨tB, mB, hP⟩ := exists_principal C m hpp
      have hw' : ∀ p, ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ Or.𝔐.t.G.hom =
          spMap (C.ψ ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ≫ jj := fun p => by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (e.ex _ p)]
        rfl
      have h1 := cubWeil_push m _ (x₀ := Over.homMk _ (hw' _)) (y₀ := Over.homMk _ (hw' _)) rfl rfl hc
      have h2 := weil_fibre Or.𝔐.t _ A φ _ u _ χ' hgp hAH tB mB hP N ζ (L₀.P w x) (L₀.P w x') hN
        ((hlat _).2 ((hper w hw _).2 ⟨x, rfl⟩)) ((hlat _).2 ((hper w hw _).2 ⟨x', rfl⟩)) _ _ (hex _).symm (hex _).symm h1
      rw [L₀.im w hw] at h2
      exact_mod_cast h2
    · obtain ⟨v, hv1, hv2⟩ := g5 τ k
      obtain ⟨v', hv1', hv2'⟩ := hv0 (τ, k)
      rw [hv2, LieModel.ValAt.unique Or.𝔐.tie.gen hv1 hv1', hv2']

end LevelTowerAlt.Val
end
end
end
