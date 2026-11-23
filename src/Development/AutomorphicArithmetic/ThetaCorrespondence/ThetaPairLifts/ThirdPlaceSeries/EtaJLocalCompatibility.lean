module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisationStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatStab

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  apply Formalism.L2.jMt_injective <;> assumption

theorem latStable_of_latInt : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  intro D M B j h1 h2 w hI v k hvk x hx
  classical
  obtain ⟨s, ϖ, hcj, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
  have hinj := jMt_injective D (D.what₂.muTw w) j
  let f : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.MtL (D.what₂.muTw w) j := fun g =>
    if h : g ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j) then h.choose else 0
  have hf : ∀ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.jMt (D.what₂.muTw w) j (f g) = g := by
    intro g hg
    have h := hI.1 g hg
    simp only [f, dif_pos h]
    exact h.choose_spec
  have key : ∀ y ∈ genSet D (D.what₂.muTw w) j, B.hK j w v k (B.iV j w y) ∈ latLoc B j w := by
    intro y hy
    obtain ⟨c, hc0, hcE⟩ := hI.2 v k s ϖ hvk hcj hu _ hy
    have e1 := B.hL_def j w h1 h2 v k s ϖ hvk hcj hu y
    rw [hcE] at e1
    have e2 := (M (D.what₂.muTw w) j h1 h2).real_inj e1
    have e3 : B.hL j w v k y = ∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, c g • f g := by
      apply hinj

      rw [e2, map_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smulₛₗ, hf g hg]

    rw [B.hK_def, e3, map_sum]
    refine Submodule.sum_mem _ fun g hg => ?_
    rw [map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w j w (c g)).1 (hc0 g)
    rw [← ho, algebraMap_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f g, ?_, rfl⟩)
    show D.what₂.jMt (D.what₂.muTw w) j (f g) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen
    rw [hf g hg]; exact hg
  have hle : latLoc B j w ≤ (latLoc B j w).comap ((B.hK j w v k).restrictScalars (B.Oc j w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  exact hle hx

end GlobalTheory.LatStab

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_integral : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  first | exact @GlobalTheory.LatStab.latStable_of_latInt | exact GlobalTheory.LatStab.latStable_of_latInt | (intros; apply GlobalTheory.LatStab.latStable_of_latInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegrality

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatTied

theorem latStable_tied : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)),
    (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) →
    ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  intro D M Tn Q hQ hI j w h1 h2 hw
  classical
  by_cases hne : (D.nd.locs j w).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hwi : D.nd.w i = w := ((D.nd.locs_mem j w i).1 hi).2
    have hQc : Tn.B.Qc j w = Q w := by rw [← Tn.Q_eq j w i hi, hQ i, hwi]
    apply GlobalTheory.T.heckeStableLocalLattice_of_integral D M Tn.B j h1 h2 w
    rw [hQc]; exact hI j h1 h2 w hw
  · have hsub : Subsingleton (heckeAlg Tn.B j w) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨I, hI'⟩ := Ideal.exists_maximal (heckeAlg Tn.B j w)
      obtain ⟨i, hi, -⟩ := Tn.mx_all j w h1 h2 hw I hI'
      exact hne ⟨i, hi⟩
    have h10 : (1 : Module.End (FractionRing (Tn.B.Oc j w)) (Tn.B.V j w)) = 0 := by
      have := congrArg Subtype.val (Subsingleton.elim (1 : heckeAlg Tn.B j w) 0)
      simpa using this
    have hx : ∀ y : Tn.B.V j w, y = 0 := fun y => by
      have := LinearMap.congr_fun h10 y
      simpa using this
    intro v k _ x _
    rw [hx (Tn.B.hK j w v k x)]
    exact Submodule.zero_mem _

end GlobalTheory.LatTied

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegralityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  first | exact @GlobalTheory.LatTied.latStable_tied | exact GlobalTheory.LatTied.latStable_tied | (intros; apply GlobalTheory.LatTied.latStable_tied <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeAdjointLeOfComp

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin

theorem prj_mul_goodOp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} (Z : Submodule K B.S.Forms) {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold Formalism.L2.DIV.goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

theorem range_adjoint_le_of_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) (e : V →ₗ[ℂ] V)
    (hs : e.IsSymmetric) (h : θ ∘ₗ e = θ) : LinearMap.range (LinearMap.adjoint θ) ≤ LinearMap.range e := by
  rintro y ⟨x, rfl⟩
  refine ⟨LinearMap.adjoint θ x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  rw [hs (LinearMap.adjoint θ x) z, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun h z
  rw [LinearMap.comp_apply] at this
  rw [this]

theorem thetaCut_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (S0 : IndefData (A.side P ψ Zs)) (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → (∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = jW i ((S0.θ i t).mulVec ((lPrj D A P ψ Zs i t).mulVec x))) → ThetaCut D (tup t) ((i : ℕ) + 1) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i t hF hθ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : lPrj D A P ψ Zs i t * lE D A P ψ i t = lPrj D A P ψ Zs i t := prj_mul_goodOp (Zs.Zl i t) hB
  refine range_adjoint_le_of_comp _ _ (D.what₂.eMt_sa _ _) ?_
  refine LinearMap.ext_on_range hF.span fun k => ?_
  rw [LinearMap.comp_apply, hF.op_eq]
  refine (hθ _).trans (Eq.trans ?_ (hθ _).symm)
  rw [Matrix.mulVec_mulVec (Pi.single k 1), hP]

end GlobalTheory.EtaJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory



theorem etaJ_join_closed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd Q hQ hLatInt hHT hHR hAV hCS jW hmR hθ
    hEig hIsot h42 hZ hGood
  have hLat : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w :=
    fun j w h1 h2 hne => GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality D M Tn Q hQ hLatInt j w h1 h2 hne
  have hTC : ∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i) := by
    intro i
    have hne := D.nd.w_tw i
    have hy : D.plEq (D.nd.w i) ∈ S0.Tw := by
      refine (hTw _).2 fun e => hne ?_
      rw [hTup.muAt, ← hTup.mu0, e]
    have htw : D.what₂.muTw (D.nd.w i) = tup (S0.μ (D.plEq (D.nd.w i))) :=
      ((D.what₂.muAt_or _).resolve_left hne).symm.trans (hTup.muAt _)
    obtain ⟨hj1, hj2⟩ := D.nd.j_range i
    let i' : Fin m := ⟨D.nd.j i - 1, by omega⟩
    have hj : D.nd.j i = (i' : ℕ) + 1 := by simp only [i']; omega
    rw [D.nd.mu_w i, htw, hj]
    exact GlobalTheory.EtaJoin.thetaCut_of_tie D G Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i' _
      (hMt i' _ hy).1 (hθ i' _ hy)
  have hSpec : ∀ i, SpecPr D i :=
    GlobalTheory.T.good_part_projector_spectral_at_every_localisation D M hHT hHR hAV Tn hStd hCS hTC hEig hIsot h42 hZ hGood
  exact GlobalTheory.etaJ_join D G Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd hLat hSpec

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegralityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  first | exact @GlobalTheory.etaJ_join_closed | exact GlobalTheory.etaJ_join_closed | (intros; apply GlobalTheory.etaJ_join_closed <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaJLocalCompatibility

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.etaJ_with_local_data_eq_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL K B f T w P hK hF hS x l big L hB hO M Tn Q hstd hQ hlat hT hR hAV hCS hE hI h42 hZ hG j v h1 h2 v' hv
  obtain rfl : v' = v := eq_of_heq hv
  have hTup : Formalism.L2.DIV.TupTie (withLoc L) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) x.r.Y.tup :=
    ⟨x.r.Y.tup0, x.r.Y.muAt, x.m.z.R.hv0, fun a b h => by rw [← x.r.Y.tupT_tup a, h, x.r.Y.tupT_tup]⟩
  have hTw : ∀ y, y ∈ ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).Tw ↔
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).μ y ≠
        (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 :=
    fun y => ⟨x.m.z.pins.char.tup.mu_ne y, fun h => by_contra fun hw => h (x.m.z.pins.char.tup.mu_off y hw)⟩
  have hθ := GlobalTheory.Mem.ThRead.theta_of_noEta GlobalTheory.Mem.ThetaRead3.thetaP_read_noEta GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth_noEta
    _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have hZ0 := GlobalTheory.Mem.R3.DivisionRationalLift.rationalReadingNoCongruence_thetaComplement_spanned _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have key := GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) _ _ _ _ (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
    x.m.z.F.P0 x.m.z.F.ψ0 ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).fam3.toSub2 (zsOf x.m.z.R x.m.z.F))
    x.r.Y.tup x.r.Y.eMt 1 x.m.intersectionNumber_baseChange.ok.ok2 le_rfl
    ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) M Tn
    hTup hTw (fun i y _ => ⟨x.r.Y.formsL i _, x.r.Y.latL i _, hZ0 i _⟩) hstd Q hQ hlat hT hR hAV hCS x.r.Z.jW rfl
    (fun i y _ x' => hθ i _ x') hE hI h42 hZ hG
  obtain ⟨i, rfl⟩ : ∃ i : Fin (Dof x).R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine (key i v').trans (Eq.trans ?_ (x.m.eta _ v'))
  unfold Rw.etaOf
  rw [dite_eq_left ⟨by omega, i.2⟩]
  split_ifs with ha hb hb
  · simp only [Nat.add_sub_cancel, Fin.eta]
    rfl
  · exact (hb ha).elim
  · exact (ha hb).elim
  · rfl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.etaJ_local_compatibility_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.etaJ_with_local_data_eq_alt | exact _root_.GlobalTheory.etaJ_with_local_data_eq_alt | (intros; apply _root_.GlobalTheory.etaJ_with_local_data_eq_alt <;> assumption)
end
end
end
end
