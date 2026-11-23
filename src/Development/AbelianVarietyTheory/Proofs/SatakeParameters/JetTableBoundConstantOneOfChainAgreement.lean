module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardDeterminantUnit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulMemLocPOfVal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VolqExistsPow
public import Formalism.LocalToGlobal.Divisibility.BrJoint
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStdSplit

section

@[expose] public section

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST (by first | exact hN | exact hN.1)
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundOfJetLoss

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem vAdd_mul_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem vAdd_pow_eq (x : K) (n : ℕ) : vAdd w (x ^ n) = n * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow]
  simp

theorem vAdd_prod_of_ne {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, vAdd_mul_of_ne w (h a) (Finset.prod_ne_zero_iff.2 fun i _ => h i), ih]

theorem vAdd_nonneg_of_le {x : K} (hx : x ≠ 0) (h : w.valuation K x ≤ 1) : 0 ≤ vAdd w x := by
  unfold vAdd
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hx) one_ne_zero).2 h
  rw [WithZero.log_one] at this
  omega

theorem mem_of_vAdd_pos {a : 𝓞 K} (h : 0 < vAdd w (a : K)) : a ∈ w.asIdeal := by
  by_contra hn
  have h1 : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hn
  rw [vAdd, h1, WithZero.log_one] at h
  omega

end Val

theorem sum_nuW_nonneg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {j : ℕ} (hj : j < R.m)
    (τ : X.Tau) : 0 ≤ ∑ a, (W.nuW u (j + 1) τ).w a := by
  obtain ⟨s, s', ⟨h1, h2, -⟩, h3⟩ := chainWeights X Pr R W u j hj
  refine Finset.sum_nonneg fun a _ => ?_
  have h4 := (W.lamTrue u (j + 1) τ).anti (show Fin.castLE (N_lt_succ R j).le a ≤ ⟨R.N j, N_lt_succ R j⟩ from a.2.le)
  rw [h2 τ _ le_rfl] at h4
  rw [← h3, ← h1]
  omega

theorem recWts_ok {D : D7} (EX : ErrX D) : (recWts EX).Ok := by
  exact
    { row_ok τ := ⟨D.hc τ, rfl⟩
      hc_row := recWts_row EX
      u_first u u' τ h := (D.hcW_first u τ h).trans (D.hcW_first u' τ h).symm
      u_last u u' τ h := (D.hcW_last u τ (by omega)).trans (D.hcW_last u' τ (by omega)).symm }

theorem emb_star_piG {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    (recFields D).emb τ (@star _ (recFields D).starE.toStar (((recPrimes EX).piG i : 𝓞 D.host.E) : D.host.E)) = tauPib EX i τ := by
  have h : ∀ x : D.host.E, @star _ (recFields D).starE.toStar x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    let _ := D.host.isCMField_hostE
    change D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [h]
  rfl

theorem vG_loss_le {D : D7} (L : SizeData₂ D) (EX : ErrX D) (hPr : (recPrimes EX).Ok) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) :
    (∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0) ∧
    LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) ≤
      (∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) + LiftErrorLocal.errC D L := by
  have hg0 : (D.host.g i : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hπ : ∀ τ, tauPib EX i τ ≠ 0 := by
    intro τ h
    have h1 : (recFields D).emb τ (((recFields D).conjO (EX.piG i) : 𝓞 D.host.E) : D.host.E) = 0 :=
      (emb_star_piG EX i τ).trans h
    have h2 : (recFields D).conjO (EX.piG i) = 0 := RingOfIntegers.ext ((map_eq_zero _).1 h1)
    have h3 := hPr.piG_norm i
    change EX.piG i * (recFields D).conjO (EX.piG i) = _ at h3
    rw [h2, mul_zero] at h3
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h3.symm)
  have e : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j = (D.host.g i : D.what₂.LL) ^ (D.R.f * D.R.N j * D.R.N (j + 1)) *
      ∏ τ, tauPib EX i τ ^ (∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat := fun j => by
    rw [← D.what₂.card_Tau]
    simp only [← emb_star_piG]
    rfl
  have hne : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0 := fun j => by
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ))
  refine ⟨hne, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hvg : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ hg0] at h1
    exact_mod_cast h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h1 : ∀ j ∈ Finset.range D.R.m, (vAdd (D.plEq w) (lossAt (Pr := recPrimes EX) (recWts EX) i u j) : ℝ) / D.what₂.places.ramIdx w ≤
      vNN EX i u (1 + j) w + D.R.f * (D.R.N D.R.m * (D.R.N D.R.m + D.R.t)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h2 : (D.R.f : ℝ) * D.R.N j * D.R.N (j + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
      exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.exp_le D j hj'
    have h3 : ∀ τ, (((∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat : ℕ) : ℝ) = nuAbs D u (1 + j) τ := fun τ => by
      rw [add_comm 1 j, partitionSize D EX u j hj' τ, ← Int.cast_natCast,
        Int.toNat_of_nonneg (sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj' τ)]
    rw [e, vAdd_mul_of_ne _ (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ)),
      vAdd_prod_of_ne _ _ _ fun τ => pow_ne_zero _ (hπ τ)]
    simp only [vAdd_pow_eq, hvg]
    push_cast
    simp only [h3]
    rw [add_div, mul_div_assoc, div_self he.ne', mul_one, vNN]
    linarith
  have h4 : 0 ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 3 * L.etaSz) := by
    have := L.etaSz_pos.le
    positivity
  unfold LiftErrorLocal.vG
  rw [vAdd_prod_of_ne _ _ _ hne, Int.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, LiftErrorLocal.lifts, LiftErrorLocal.errC,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  nlinarith

end GlobalTheory.ColPeriod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound : JetSplitAmb → ∀ (D : D7) (EX : ErrX D) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  first | exact @GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | exact GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | (intros; apply GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriodTies

theorem boundAt_of_chainTie (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Integrality) (hJ : JetLossAll D EX sel B χ cD) (hC : 1 ≤ C1)
    (hH : HostTie EX) (hCT : CharTie Ch mu0 eta sel) (hA : AnTie D δ χ cD) (i : Fin 2) (hS : SizeAt D i)
    (w : LiftErrorLocal.Pl D) (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hCh : ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ) :
    BoundAt L EX C1 i w u μ := by
  classical
  obtain ⟨-, hTied, -, hsel⟩ := hCT
  obtain ⟨ξ, cst, I, hI, b, hY, hK, hF, hP, eM, jA, -, -, hrat, hcol, hrow, hper⟩ := hCh
  rintro φ hφ F ⟨c, hc⟩
  have hX := hH.2.2.2.1.ok
  have hPr := hH.2.2.2.2
  obtain ⟨hne, hloss⟩ := vG_loss_le L EX hPr i w hw u
  choose! x hx using hrow.2.2.1
  have hxF : jA (∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.OtoLL (c v) • x v) = F := by

    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun v hv => by rw [LinearMap.map_smulₛₗ, hx v hv]; rfl
  have hxM := (hrow.2.2.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, hxF.trans hc⟩
  refine ⟨_, (hxF ▸ hper φ _).symm, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hg : ((D.host.g i : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
    refine mem_of_vAdd_pos _ ?_
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero)] at h1
    have h2 : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
    have h3 : (((D.host.g i : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.host.g i : D.what₂.LL) := map_natCast (algebraMap _ _) _
    rw [h3, h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hTS : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hgS : ∀ k, (recPrimes EX).g k ∈ badS D := fun k => by
    fin_cases k <;> simp [badS, hostS]
  have hb : 2 * (recFields D).f * D.R.N D.R.m + 1 < D.host.g i := by
    rw [show (recFields D).f = D.R.f from D.what₂.card_Tau]
    exact hS.1
  have hdeg : ∀ j < D.R.m, (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 1 < (D.host.g i : ℤ) := by
    intro j hj
    have h1 := (hS.2 u (j + 1) (Finset.mem_Icc.2 ⟨by omega, hj⟩)).1
    have h2 : LiftErrorLocal.Dpi D u (j + 1) = ((∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun τ _ => partitionSize D EX u j hj τ
    have h3 := Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj τ
    rw [h2] at h1
    have h4 : 2 * (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 2 < (D.host.g i : ℤ) := by exact_mod_cast h1
    omega
  have hcolb := colMu_bound_all (recWts EX) Ch sel ξ cst I _ (hJ hH hsel hA) GlobalTheory.JetOpWeylLat.jetOpWeyl chainWeights stdMove levelPrimes
    (scalarUnit_of levelPrimes heckeUnit twistUnit) entryAtG (EntQ.entryAtQ volumeAtQ) TopTwist.topAtQ hX hPr hsel u hTS hgS hI
    hTied b hY (Formalism.L2.Col.rPsymF Ch) hK hF i (D.plEq w) hg
    (fun j hj b' => wtUnit_chF (recWts EX) sel ξ I hX u hF (hPr.g_prime i) hb _ hg hj b') hdeg hrat _ ((hcol φ).1 hφ)
  have hm := GlobalTheory.BranchMembers.members _ _ _ (recWts EX) (recWts_ok EX) u
  have hval := valuation_PtilE_le_one (recWts EX) Ch sel ξ hX hPr hsel u hTS (hB _ _ _ _ _ _ _) (fun τ => (hm τ).1)
    (fun τ => (hm τ).2) (Formalism.L2.Col.rPsymF Ch) hP (hPr.g_prime i) (hPr.T_ne_g u i) hb (D.plEq w) hg
    ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) • _) hcolb _ hxM
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hval
  suffices key : ∀ y : D.what₂.LL, (D.plEq w).valuation D.what₂.LL
      ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) * y) ≤ 1 →
      y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y from key _ hval
  intro y hval
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have hc0 := Finset.prod_ne_zero_iff.2 fun j (_ : j ∈ Finset.range D.R.m) => hne j
  have h1 := vAdd_nonneg_of_le _ (mul_ne_zero hc0 hy) hval
  rw [vAdd_mul_of_ne _ hc0 hy] at h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : 0 ≤ LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) + LiftErrorLocal.vG D w y := by
    unfold LiftErrorLocal.vG
    rw [← add_div]
    exact div_nonneg (by exact_mod_cast h1) he.le
  have h3 : 0 ≤ LiftErrorLocal.errC D L := by
    have := L.etaSz_pos.le
    unfold LiftErrorLocal.errC
    positivity
  nlinarith

theorem boundAt_of_ties : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup),
    TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word,
      D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  intro hJS D L EX Dx μ ⟨Ch, mu0, eta, sel, δ, B, χ, cD, hH, hCT, hA, hCh⟩ i hS w hw u _
  have hJ : JetLossAll D EX sel B χ cD := GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound hJS D EX sel δ B χ cD
  exact boundAt_of_chainTie D L EX Dx Ch mu0 eta sel B χ cD 1
    (GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs) hJ le_rfl
    hH hCT hA i hS w hw u μ (hCh u)

end GlobalTheory.ColPeriodTies

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreemeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup), TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  first | exact @GlobalTheory.ColPeriodTies.boundAt_of_ties | exact GlobalTheory.ColPeriodTies.boundAt_of_ties | (intros; apply GlobalTheory.ColPeriodTies.boundAt_of_ties <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

namespace GlobalTheory.AtG

theorem jetTableBound_constantOne_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D),
    (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) →
    Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  intro hJ D L EX Dx hT hS i w hw u hu μ hμ
  exact GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement hJ D L EX Dx μ (hT μ hμ) i (hS i) w hw u hu

end GlobalTheory.AtG
end
end
