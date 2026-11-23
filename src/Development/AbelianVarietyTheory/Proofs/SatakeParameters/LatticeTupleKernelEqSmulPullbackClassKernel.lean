module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevelStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClassesStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunction
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesHasReaderLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLawsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesHasReaderLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelic

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]



theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dite_eq_left ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelicStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  first | exact @GlobalTheory.TwV.DelB.kerTh_pair_eq | exact GlobalTheory.TwV.DelB.kerTh_pair_eq | (intros; apply GlobalTheory.TwV.DelB.kerTh_pair_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunctionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  first | exact @GlobalTheory.TwU.SeamKer.seam_kerTh | exact GlobalTheory.TwU.SeamKer.seam_kerTh | (intros; apply GlobalTheory.TwU.SeamKer.seam_kerTh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTranspor

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hTie
  exact GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c')
    (GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTransporStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  first | exact @GlobalTheory.TwV.th_eq_kerTh | exact GlobalTheory.TwV.th_eq_kerTh | (intros; apply GlobalTheory.TwV.th_eq_kerTh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKe

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV.SPull

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_scal {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun v => k * Φ v) e z = k * xiL H α vol SX SA SB Φ e z := by
  have hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w := by
    intro x
    funext w
    unfold xiS Formalism.L2.Th1.H.sumU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y := by
      unfold hatS
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    beta_reduce
    rw [this]
    ring
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS x]
  simp only [Formalism.L2.Th1.H.opU]
  ring

theorem kerTh_scal {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k : ℂ) (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl N N' (fun x => k * Ξ x) z = k * kerTh B χ SS cl N N' Ξ z := by
  have hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) =
      fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v := by
    funext v
    unfold Formalism.L2.Ker.onV
    split_ifs <;> simp
  unfold kerTh thC xiV
  rw [hon]
  exact xiL_scal _ _ _ _ _ _ _ _ _ _

theorem kerTh_prop {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ Ξ' : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k k' : ℂ)
    (h : ∀ x, k * Ξ x = k' * Ξ' x) (z : TaylorLogMetric.VC D a b) :
    k * kerTh B χ SS cl N N' Ξ z = k' * kerTh B χ SS cl N N' Ξ' z := by
  rw [← kerTh_scal, ← kerTh_scal, funext h]



theorem kerTh_eq_pull : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' z
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hSS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hA
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA i (Nat.le_of_succ_le hi) γ hγ
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA (i + 1) hi γ' hγ'
  have hN := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA i (Nat.le_of_succ_le hi) c x γ hγ κ hx
  have hN' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA (i + 1) hi c' x' γ' hγ' κ' hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hu'
  have hc := GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hA Xi muT law i hi c c'
  have hth := GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported A dtU a hP hA Xi muT law i hi c c'
  have hmv := GlobalTheory.TwU.KerMove.kerTh_move D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (ssRec t u μ) (t.rd u μ).lev hl hSS
    _ _ _ _ _ (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c') hc _ _ hu hu'
  rw [hth, ← hmv, hN, hN']
  exact kerTh_prop _ _ _ _ _ _ _ _ _ _ hd z

end GlobalTheory.TwV.SPull

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  first | exact @GlobalTheory.TwV.SPull.kerTh_eq_pull | exact GlobalTheory.TwV.SPull.kerTh_eq_pull | (intros; apply GlobalTheory.TwV.SPull.kerTh_eq_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem reV_pull_submatrix {D : D7} (T : TaylorLogMetric.Tor D) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    (e : Matrix (Fin N) (Fin N) D.host.E) (e' : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    reV ha hb (TaylorLogMetric.pull D T e e' G) =
      TaylorLogMetric.pull D T (e.submatrix (Fin.cast ha) (Fin.cast ha)) (e'.submatrix (Fin.cast hb) (Fin.cast hb)) (reV ha hb G) := by
  subst ha hb
  rfl

theorem pullAt_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  intro D _ _ _ _ _ _ _ _ u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa' z
  have hj1 : j + 1 ≤ D.R.m := hj
  have hj0 : j ≤ D.R.m := Nat.le_of_succ_le hj1
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  rw [GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic S hD j hj1 (hr j) (hr (j + 1)) La La' hLa hLa']
  have hV := GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj1 (clsAt X H j La.1 La.2)
    (clsAt X H (j + 1) La'.1 La'.2) (J.pt std j _ La) (J.pt std (j + 1) hj1 La') (d.gam j _ La) (d.mem j _ La)
    (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap j _ La) (d.kap (j + 1) hj1 La') (d.eq j _ La hLa) (d.eq _ _ La' hLa')
  have hN := (GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j + 1) hj1 (clsAt X H (j + 1) La'.1 La'.2)
    (J.pt std (j + 1) hj1 La') (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap (j + 1) hj1 La') (d.eq _ _ La' hLa')).2.2
  have e1 : d.eM j La = (gMat J j hj0 (d.gam j hj0 La)).submatrix (Fin.cast (hr j)) (Fin.cast (hr j)) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj0, hr j⟩]
  have e2 : d.eM (j + 1) La' = (gMat J (j + 1) hj1 (d.gam (j + 1) hj1 La')).submatrix (Fin.cast (hr (j + 1))) (Fin.cast (hr (j + 1))) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj1, hr (j + 1)⟩]
  have e3 : thCl (X := sysS H X std) t u μ (clsAt X H) j La La' =
      reV (hr j) (hr (j + 1)) ((t.rd u μ).Th t.seam t.amb j (clsAt X H j La.1 La.2) (clsAt X H (j + 1) La'.1 La'.2)) := by
    unfold thCl; rw [dite_eq_left ⟨hr j, hr (j + 1)⟩]
  have e4 : d.sP S j La La' = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap j hj0 La).1) * d.chi (j + 1) hj1 La' /
      (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap (j + 1) hj1 La').1) * d.chi j hj0 La) := by
    unfold Dec.sP; rw [dite_eq_left hj1]
  rw [e1, e2, e3, e4, ← reV_pull_submatrix]
  have key : ∀ a b c e k p : ℂ, c ≠ 0 → e ≠ 0 → c * e * k = a * b * p → k = a * b / (c * e) * p := by
    intro a b c e k p hc he h
    field_simp
    linear_combination h
  exact key _ _ _ _ _ _ hN (Units.ne_zero _)
    (hV (fun τ i k => z τ (Fin.cast (hr (j + 1)).symm i) (Fin.cast (hr j).symm k)))

end GlobalTheory.TwV.DelB
end
end
end
