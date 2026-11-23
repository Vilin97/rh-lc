module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffPrimeKernelLatticesOfAgreeAwayStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverPStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Ideal.Int
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.AlgebraMapFinite
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPointsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeNotStable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdeleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddingsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhereStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_unif | exact GlobalTheory.TwV.Xc.Unif.exists_unif | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationInverseHalfDifferentEqOneUnramified

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem not_dvd_absDifferent_of_not_mem_sq {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) =
      Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P.asIdeal := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]
    exact h1
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime P.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := hP.eq_of_le hne le_sup_left
    have hQP : Q ≤ P.asIdeal := heq ▸ le_sup_right
    apply h2
    have hmem : ((p : ℕ) : 𝓞 E) ∈
        Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [hQ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hQP hmem
  exact not_dvd_differentIdeal_of_isCoprime ℤ P.asIdeal Q hcop hQ.symm

theorem inverseHalfDifferent_local_trivial_at_prime_norm : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D p hp P h1 h2
  have hnd := not_dvd_absDifferent_of_not_mem_sq p hp P h1 h2
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hspec : D.host.𝔟 ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := ⟨_, D.host.𝔟_spec.1⟩
  have hn : ¬ D.host.𝔟 ≤ P.asIdeal := fun h => hnd (by
    rw [ht]
    exact ((Ideal.dvd_iff_le.2 h).trans hspec).mul_right _)
  obtain ⟨t, htb, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim htP hs, ?_⟩
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hb).1 hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ htb))
    rw [Submodule.mem_one]
    refine ⟨u, ?_⟩
    rw [hu, mul_smul, Algebra.smul_def t, mul_comm]
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 hx
    refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
    obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨u * z, by rw [map_mul, hu]⟩

end GlobalTheory.TwV.Xc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationInverseHalfDifferentEqOneUnramifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem _root_.GlobalTheory.T.localisation_inverseHalfDifferent_eq_one_unramified : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  first | exact @GlobalTheory.TwV.Xc.inverseHalfDifferent_local_trivial_at_prime_norm | exact GlobalTheory.TwV.Xc.inverseHalfDifferent_local_trivial_at_prime_norm | (intros; apply GlobalTheory.TwV.Xc.inverseHalfDifferent_local_trivial_at_prime_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAway

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Xc.xiM_eq_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb La' Lb' hab hab'
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hj1 : j + 1 ≤ D.R.m := hj
  funext z
  rw [GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) La La' z, GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) Lb Lb' z]
  have hc : J.chart std j (Nat.le_of_succ_le hj1) La = J.chart std j (Nat.le_of_succ_le hj1) Lb := by
    obtain ⟨h1, h2, h3, -⟩ := hab
    rcases La with ⟨c, a⟩
    rcases Lb with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j _ c a b h1 h2
  have hc' : J.chart std (j + 1) hj1 La' = J.chart std (j + 1) hj1 Lb' := by
    obtain ⟨h1, h2, h3, -⟩ := hab'
    rcases La' with ⟨c, a⟩
    rcases Lb' with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS (j + 1) _ c a b h1 h2
  rw [hc, hc']
  refine congrFun (S.law.away j hj1 _ _ (J.pt std j _ Lb) (J.pt std (j + 1) hj1 Lb') (J.pt std j _ La) (J.pt std (j + 1) hj1 La') ?_) _
  intro v' hv'
  have hne : v' ≠ ((A0 J).pl v).1 := fun h => (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hS).2.2.1 v' hv' (h ▸ ((A0 J).pl v).2)
  exact ⟨(GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j _ La Lb hab).1 v' hne, (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v (j + 1) hj1 La' Lb' hab').1 v' hne⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAwayStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  first | exact @GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | exact GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.xiM_eq_of_sameAway <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePair

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.AwayInd



theorem away_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → S.Pos → S.Pair → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hK hPos hPair
  intro v j hj
  have hgood := J.one.good
  have hint := J.one.int
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  obtain ⟨hcop, hSS, -, -⟩ := GlobalTheory.T.level_badPrimes_coprime_residueChar S hDict hSpl
  obtain ⟨P, hPof, happ, hpP, hpP2⟩ := GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP _ _ _ _ _ (A0 J) hint hSpl.1 v
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.XcSplit.prime_not_stable _ _ (sigD D) _ _ _ (A0 J) _ hgood hint hSpl.1 v P hPof
  have hpC : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, map_natCast]; exact hpP
  have hcopE : IsCoprime (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) := by
    have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
    simpa using h
  have hlev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hpQ hlQ
    obtain ⟨x, y, hxy⟩ := hcopE
    have h1 : (1 : 𝓞 D.host.E) ∈ Q.asIdeal := hxy ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left x hlQ) (Q.asIdeal.mul_mem_left y hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hab' : (b : D.host.E) = D.host.conj (a : D.host.E) := by
    rw [hab]
    first | exact Formalism.L2.PairingIndexBounds.F.sig_conj D _ | exact Formalism.L2.Fam.sig_eq_conj D.host D.sp.cm _ | exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  refine ⟨P, ⟨a, b, hab', ha, hb⟩, GlobalTheory.T.localisation_inverseHalfDifferent_eq_one_unramified D _ hp P hpP hpP2, fun h => hSS P h hpP, fun h => hSS _ h hpC,
    hlev P hpP, hlev _ hpC, hPof, happ, ?_⟩
  by_cases hc : Nonempty ((sysS H X std).Lv.comp j) ∧ Nonempty ((sysS H X std).Lv.comp (j + 1))
  · obtain ⟨⟨c⟩, ⟨c'⟩⟩ := hc
    obtain ⟨π, hπU, hoff, hord⟩ := GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere _ _ (sigD D) _ _ _ (A0 J) _ hgood v
    have hU : IsUnifAt J v π := ⟨hπU, hoff, hord⟩
    obtain ⟨x, y, hx0, hy0, hx, hy⟩ := GlobalTheory.T.two_units_at_place_uniformizing_idele S hDict hSpl hK hPos v π hU j hj c c'
    refine ⟨x, y, hx0, hy0, ?_⟩
    intro La Lb La' Lb' h1 h2 h3 h4 haw
    have e1 : La.1 = Lb.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.1) haw
    have e2 : Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.2) haw
    have e3 : La'.1 = Lb'.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.1) haw
    have e4 : Function.update La'.2 ((sysS H X std).vJ (j + 1) v) ⊥ = Function.update Lb'.2 ((sysS H X std).vJ (j + 1) v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.2) haw
    have hA : SameAway (hT := hT) (H := H) (X := X) std v j La Lb := ⟨h1, h3, e1, e2⟩
    have hA' : SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' := ⟨h2, h4, e3, e4⟩
    refine ⟨GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof j hj.le La Lb hA, GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof (j + 1) hj La' Lb' hA', ?_, ?_,
      GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway S hDict hSpl v j hj La Lb La' Lb' hA hA', GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace S hDict hSpl hPair v π hU j hj x y hx hy La Lb La' Lb' hA hA'⟩
    · have hLb : Lb = (La.1, Lb.2) := Prod.ext e1.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl j La.1 La.2 Lb.2
    · have hLb : Lb' = (La'.1, Lb'.2) := Prod.ext e3.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl (j + 1) La'.1 La'.2 Lb'.2
  · have h1 : (sysS H X std).vEqK 1 0 := GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb 1 (by simp)
    refine ⟨1, 1, h1, h1, ?_⟩
    intro La Lb La' Lb'
    exact absurd ⟨⟨La.1⟩, ⟨La'.1⟩⟩ hc

end GlobalTheory.TwV.Xc.AwayInd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePairStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_away_of_positive_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → S.Pair → S.Away) := by
  first | exact @GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair | exact GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverP

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem away_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact GlobalTheory.T.kernelSite_away_of_positive_pair S hD ⟨J.alg0, J.alg⟩ J.kin (GlobalTheory.T.site_place_induces_position_embeddings S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hD)

end GlobalTheory.TwV
end
end
