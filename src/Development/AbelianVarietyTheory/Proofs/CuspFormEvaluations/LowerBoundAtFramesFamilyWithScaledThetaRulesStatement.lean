module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsOrthoFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NegLogSqrtLeOfJbound
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProductStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  first | exact @GlobalTheory.BlockRen.blockProd_rename | exact GlobalTheory.BlockRen.blockProd_rename | (intros; apply GlobalTheory.BlockRen.blockProd_rename <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinsetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  first | exact @GlobalTheory.ThetaLower.thetaRule_sum_lower | exact GlobalTheory.ThetaLower.thetaRule_sum_lower | (intros; apply GlobalTheory.ThetaLower.thetaRule_sum_lower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRul

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem totalDegree_eq_sum_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (h0 : P ≠ 0) (hh : P.IsHomogeneous P.totalDegree) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h0
  have hr := hP.1.2.2 m hm
  have h1 := hh (MvPolynomial.mem_support_iff.1 hm)
  have h2 : m.degree = P.totalDegree := by rw [Finsupp.degree_eq_weight_one]; exact h1
  rw [← h2, Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hr τ i

theorem lieFac_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (x : ℝ) (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) (d : ℕ) (hd : d = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) :
    lieFac Dw x a ^ 2 = ((2 * Real.pi * x)⁻¹) ^ d := by
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hd' : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = d := by rw [hd]; push_cast; rfl
  unfold lieFac
  rw [hd', ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  push_cast
  ring

theorem i2iAt_of_containsTh : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  intro hCI E _ _ _ H Dw l Xo c _ r U xR nab hnab hU α hα hMb a n P₁ hdom hP hbp s hs N wR hw hct R0 m hrun hm
    tableLineDegreeFive cc hP14 hcc σ hσ k x hx
  classical
  obtain ⟨hUn, hFT, hxi⟩ := hU σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := exists_ortho_frame E r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound hCI E H Dw l Xo c σ r (U σ) k ⟨_, hbd⟩ xR nab hnab hσ hUn
    (hFT k _) hbo (hxi k) α hα hMb a n P₁ hP hbp R0 m hrun hm
  obtain ⟨h0, hh, -⟩ := GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial E H Dw n c.F σ P₁ hbp Dw.mult id (fun _ => le_rfl) Function.injective_id
  have hdeg := totalDegree_eq_sum_rows c a n P₁ hP h0 hh
  have hxR : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxi k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hM : (0 : ℝ) < l.M := by
    have := Pr.hq
    rw [hq] at this
    exact_mod_cast this
  obtain ⟨jb, hjb, hf⟩ := hct
  choose f hf1 hf2 using hf
  haveI : Finite (LevQ Dw l) := (GlobalTheory.card_levQ E H Dw l).1
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hb := hbound f hf1
  rw [finsum_eq_sum_of_fintype] at hb
  have hrec : ∀ j, recNrm (U σ) xR a n (wR j) k x =
      lieFac Dw xR a * ‖rdU (U σ) (wR j) k (FD.rmul x b)‖ := fun j => by
    unfold recNrm
    rw [hpn _ _ (hUn.2.2.2.2.1 a n hdom (wR j) (hw j) k)]
  have hval : ∀ q, rdU (U σ) (wR (jb q)) k (FD.rmul x b) =
      σ s * toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩)) := fun q => by
    have e : wR (jb q) = s • f q := by
      funext p y
      rw [hf2 q p y]
      exact (Algebra.smul_def s (f q p y)).symm
    rw [e, map_smulₛₗ]
    show σ s * rdU (U σ) (f q) k (FD.rmul x b) = _
    congr 1
    exact dif_pos hbd
  have hkey : (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ j, recNrm (U σ) xR a n (wR j) k x ^ 2 := by
    have hl := lieFac_sq Dw xR hxR a _ hdeg
    have hL : (0 : ℝ) ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree := by positivity
    calc (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n
        = ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ((2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hL
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * (‖σ s‖ ^ 2 *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs σ)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL
      _ = ∑ q, recNrm (U σ) xR a n (wR (jb q)) k x ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hrec, hval, mul_pow, hl, norm_mul, mul_pow]
      _ = ∑ j ∈ Finset.univ.image jb, recNrm (U σ) xR a n (wR j) k x ^ 2 :=
          (Finset.sum_image (f := fun j => recNrm (U σ) xR a n (wR j) k x ^ 2) fun _ _ _ _ h => hjb h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hfin := neg_log_sqrt_le_of_jbound E T P₁.totalDegree n Pr _ tableLineDegreeFive cc hkey (by rw [hTr, hPm]; exact hP14)
    (by rw [hPm, hq]; exact hcc)
  rw [hph] at hfin
  rw [← hphi]
  exact hfin

end GlobalTheory.AnVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  first | exact @GlobalTheory.AnVal.i2iAt_of_containsTh | exact GlobalTheory.AnVal.i2iAt_of_containsTh | (intros; apply GlobalTheory.AnVal.i2iAt_of_containsTh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRulesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lower_bound_at_frames_family_with_scaled_thetaRules : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  first | exact @GlobalTheory.DegreeInterpolationBounds.i2iAt_record | exact GlobalTheory.DegreeInterpolationBounds.i2iAt_record | (intros; apply GlobalTheory.DegreeInterpolationBounds.i2iAt_record <;> assumption)
end
end
