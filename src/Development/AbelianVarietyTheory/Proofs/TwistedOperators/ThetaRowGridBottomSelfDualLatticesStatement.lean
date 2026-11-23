module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbeddingStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLatticeCongruenceMemConjugateIdealInfStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignature

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSylvester

theorem neg_card_eq_sig : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau),
    (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  intro D V hV A τ
  set ε := A.ε τ with hε
  set a := (Finset.univ.filter fun i => ε i = true).card with ha_def
  set b := (Finset.univ.filter fun i => ε i = false).card with hb_def
  have ha : Fintype.card {i // ε i = true} = a := by rw [Fintype.card_subtype]
  have hb : Fintype.card {i // ¬ ε i = true} = b := by
    rw [Fintype.card_subtype]; simp [b]
  let e0 : Fin V.rank ≃ Fin a ⊕ Fin b :=
    (Equiv.sumCompl (fun i => ε i = true)).symm.trans
      (Equiv.sumCongr (Fintype.equivFinOfCardEq ha) (Fintype.equivFinOfCardEq hb))
  have hl : ∀ k : Fin a, ε (e0.symm (Sum.inl k)) = true := fun k => by
    simp [e0]
    exact ((Fintype.equivFinOfCardEq ha).symm k).2
  have hr : ∀ k : Fin b, ε (e0.symm (Sum.inr k)) = false := fun k => by
    simp [e0]
    simpa using ((Fintype.equivFinOfCardEq hb).symm k).2
  have hcard : Fintype.card (Fin V.rank) = a + b := by simpa using Fintype.card_congr e0
  set F := A.fr τ with hF_def
  have hF : IsUnit F := A.fr_unit τ
  have hFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hF)
  have hJ : (F⁻¹)ᴴ * gramAt D V τ * F⁻¹ = Formalism.REAL.Jm ε := by
    rw [← A.fr_gram τ]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = (F * F⁻¹)ᴴ * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFi]; simp
  let Q : Matrix (Fin V.rank) (Fin a ⊕ Fin b) ℂ := (F⁻¹).submatrix id e0.symm
  have hQ : Qᴴ * gramAt D V τ * Q = Formalism.UG.Jpq a b := by
    have h2 : Qᴴ * gramAt D V τ * Q = ((F⁻¹)ᴴ * gramAt D V τ * F⁻¹).submatrix e0.symm e0.symm := by
      ext r s; simp only [Q, Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]
    rw [h2, hJ]
    ext (r | r) (s | s) <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, e0.symm.injective.eq_iff] <;>
      split_ifs <;> simp
  have hsig1 : Formalism.UG.HasSignature (V.gram.map (tauE D τ)) a b :=
    GlobalTheory.FrameComplement.hasSignature_of_frame hcard Q hQ
  have hsig2 := hV (tauE D τ)
  have heq : a = (V.sig (tauE D τ)).1 := GlobalTheory.SylvesterInertia.hasSignature_fst_unique hsig1 hsig2
  obtain ⟨e2, _, _⟩ := hsig2
  have h2 : V.rank = (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 := by simpa using Fintype.card_congr e2
  have h3 : V.rank = a + b := by simpa using hcard
  omega

end GlobalTheory.FrameSylvester
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignatureStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau), (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  first | exact @GlobalTheory.FrameSylvester.neg_card_eq_sig | exact GlobalTheory.FrameSylvester.neg_card_eq_sig | (intros; apply GlobalTheory.FrameSylvester.neg_card_eq_sig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusInfConjLeSpanTypePrimesProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

theorem le_of_le_primes {R : Type} [CommRing R] [IsDedekindDomain R] {I J : Ideal R} (hJ : Squarefree J)
    (h : ∀ P : Ideal R, P.IsPrime → J ≤ P → I ≤ P) : I ≤ J := by
  have hrad : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P hP => h P hP.2 hP.1
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact Ideal.le_of_dvd (hJ.isRadical n I (Ideal.dvd_iff_le.2 hn))

theorem squarefree_span_g (D : D7) (k : Fin 2) :
    Squarefree (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}) := by
  have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (g_splits D k).2

end GlobalTheory.ModulConj

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

theorem inf_le_place {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (k : Fin 2)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    G.modul ⊓ D.host.conj • G.modul ≤ P.asIdeal := by
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have hS : P.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  set v := P.under (𝓞 D.host.F) with hvdef
  have hw : (G.pl.w v).under (𝓞 D.host.F) = v := G.pl.under_w hS
  have hmod : G.modul ≤ (G.pl.w v).asIdeal := by
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v ∣ G.modul := Finset.dvd_prod_of_mem _ hS
    exact (Ideal.le_of_dvd hd).trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := G.pl.w v) (Q := P) (by rw [hw]) with h | h
  · rw [h]
    exact inf_le_left.trans hmod
  · rw [h]
    intro x hx
    have hx2 := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 (Ideal.mem_inf.1 hx).2
    have hy : D.host.conj⁻¹ • x ∈ (G.pl.w v).asIdeal := hmod hx2
    have e : Formalism.DivisionValues.cO D.host.E (D.host.conj⁻¹ • x) = x := by
      apply RingOfIntegers.ext
      show star ((D.host.conj⁻¹ • x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E)
      rw [GlobalTheory.TypePlaces.star_eq_conj]
      exact D.host.conj.apply_symm_apply (x : D.host.E)
    show x ∈ (G.pl.w v).asIdeal.map (Formalism.DivisionValues.cO D.host.E)
    rw [← e]
    exact Ideal.mem_map_of_mem _ hy

theorem modul_inf_conj_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc),
    G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  intro D T L sc G
  have hk : ∀ k : Fin 2, G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
    intro k
    refine le_of_le_primes (squarefree_span_g D k) fun Q hQ hle => ?_
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q := hle (Ideal.subset_span rfl)
    have hne : Q ≠ ⊥ := by
      rintro rfl
      exact (D.host.g_prime k).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hg))
    exact inf_le_place G k ⟨Q, hQ, hne⟩ hg
  have hco : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  intro x hx
  rw [Ideal.mem_span_singleton, Nat.cast_mul]
  exact hco.mul_dvd (Ideal.mem_span_singleton.1 (hk 0 hx)) (Ideal.mem_span_singleton.1 (hk 1 hx))

end GlobalTheory.ModulConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusInfConjLeSpanTypePrimesProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  first | exact @GlobalTheory.ModulConj.modul_inf_conj_le | exact GlobalTheory.ModulConj.modul_inf_conj_le | (intros; apply GlobalTheory.ModulConj.modul_inf_conj_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomGrid

theorem bottom : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  intro D _ T L μ0 hL sc G W M _
  have hY : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV (Node.rank D (.grid 0 0)) (Node.neg D.R.m (.grid 0 0)) :=
    node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := G.sp.P_is 0 (Nat.zero_le _)
  refine ⟨hY.sd, hP.sd, G.sp.lat0, ?_, ?_, ?_, ?_, ?_⟩
  · show zv G.sp.dec0 ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun p => ?_, ?_⟩
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    · funext i
      simp [zv, Matrix.mulVec, dotProduct]
  · intro k hk hfin
    have h1 : Lev.finE (Yc D 0) k ∈ congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) G.modul := by
      refine GlobalTheory.T.congruence_level_of_embedding G.sp.dec0 (L.ΛY 0) (fun _ => 1) G.modul k ?_
      have e : G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := G.sp.lat0
      have := hfin
      unfold GridData.levCong at this
      rw [e] at this
      exact this
    have h2 := GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf (Yc D 0) (L.ΛY 0) hY.sd _ _ h1
    exact Subgroup.mem_inf.2 ⟨hk, congLev_mono (GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product G) h2⟩
  · simpa [Node.rank, rankV] using hY.rank
  · simpa [Node.rank, rankP, nRk] using hP.rank
  · intro A τ
    rw [GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature _ hY.sigOK A τ, hY.sig]
    simp only [Node.neg, Nat.sub_zero]
    exact Nat.div_le_self _ _
end GlobalTheory.BottomGrid
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  first | exact @GlobalTheory.BottomGrid.bottom | exact GlobalTheory.BottomGrid.bottom | (intros; apply GlobalTheory.BottomGrid.bottom <;> assumption)
end
end
