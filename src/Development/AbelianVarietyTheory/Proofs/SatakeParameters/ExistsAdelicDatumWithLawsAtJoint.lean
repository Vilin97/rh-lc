module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumInvarianceSupportKernelChainStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumSourceLevelLawStatement
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicFiniteDatumIntegralOffBadPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentativesStatement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChainStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesFirstCoupledSteStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesMatrixStepStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixStepsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivarianceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStep

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.AdLevCpl

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem levAt_coupled : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hMu i hi hi2 hAw
  have key : ∀ β β' x x' p p', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' → ∀ z,
      xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
    intro β β' x x' p p' hp hp' z
    have hh : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
    unfold xiAd
    rw [dite_eq_left hh]
    rw [hAw β β' x x' x x' p p' hh.1.choose hh.2.choose hp hp' hh.1.choose_spec hh.2.choose_spec (fun v _ => ⟨rfl, rfl⟩)]
  intro β β' x x' x₁ x₁' κ κ' h1 h1' z
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  obtain ⟨p₁, hp₁⟩ := hEx i (Nat.le_of_succ_le hi) β x₁
  obtain ⟨p₁', hp₁'⟩ := hEx (i + 1) hi β' x₁'
  rw [key β β' x₁ x₁' p₁ p₁' hp₁ hp₁' z, key β β' x x' p p' hp hp' z]
  have hs := GlobalTheory.T.firstCoupledStep_adelicDatum_source_level_law A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x₁ x₁' κ p p₁' p₁ h1 hp hp₁' hp₁ (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  have ht := GlobalTheory.T.firstCoupledStep_adelicDatum_law_targetLevel A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' h1' hp hp' hp₁' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  linear_combination (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1)) * hs +
    (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1)) * ht

end GlobalTheory.AdLevCpl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStepStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.AdLevCpl.levAt_coupled | exact GlobalTheory.AdLevCpl.levAt_coupled | (intros; apply GlobalTheory.AdLevCpl.levAt_coupled <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem smul_sub_mem_of_frames {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Sp E n)} {fr : Frs E n SB} (hf : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr) (P : SB) (s : E) (a b y₀ : Sp E n)
    (ha : ∀ l, IntAt P.1 (s * ((fr P).symm a - y₀) l)) (hb : ∀ l, IntAt P.1 (s * ((fr P).symm b - y₀) l)) :
    s • (a - b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  have h : s • (fr P).symm (a - b) ∈ stdAt E n P.1 := GlobalTheory.TopStep.mem_stdAt.2 fun l => by
    have := GlobalTheory.TopStep.intAt_sub (ha l) (hb l)
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    ring
  have := (hf P _).2 h
  rwa [map_smul, LinearEquiv.apply_symm_apply] at this

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem chartBaseRepresentative_penultimate_step (A : AdData t u μ St) (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ) :
    y0At A (t.m2 + 1) hi β P = A.y0 β P := by
  unfold y0At
  rw [dite_eq_left rfl]

end

theorem cosetOf_eq_yb : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c
  obtain ⟨w, -, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  ext y
  constructor
  · intro hy
    rw [hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_comap]
    have h1 := hy P
    have h2 := H.coset c w hwm P
    rw [chartBaseRepresentative_penultimate_step] at h1
    unfold SameCoset at h1 h2
    have key := smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2
    by_cases hP : P.1 ∈ t.Pr.vGs
    · simp only [hP, if_true] at key ⊢
      simpa using key
    · simp only [hP, if_false] at key ⊢
      simpa [zpow_natCast] using key
  · intro hy P
    rw [chartBaseRepresentative_penultimate_step]
    exact H.coset c y hy P

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCosetStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.couplingCoset_eq_chartPointCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  first | exact @GlobalTheory.TwV.cosetOf_eq_yb | exact GlobalTheory.TwV.cosetOf_eq_yb | (intros; apply GlobalTheory.TwV.cosetOf_eq_yb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  first | exact @GlobalTheory.TwV.MuLawPf.muLaw_underTie | exact GlobalTheory.TwV.MuLawPf.muLaw_underTie | (intros; apply GlobalTheory.TwV.MuLawPf.muLaw_underTie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernel

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {a : 𝓞 D.host.E}

theorem xiAd_eq_of_isPtAd (hW : ∀ i hi, PtAway A a i hi) {i : ℕ} {hi : i + 1 ≤ D.R.m}
    {β : (St i (Nat.le_of_succ_le hi)).Ch} {β' : (St (i + 1) hi).Ch} {x : UA D i (Nat.le_of_succ_le hi)} {x' : UA D (i + 1) hi}
    {p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i} {p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)}
    (hp : IsPtAd A a i (Nat.le_of_succ_le hi) β x p) (hp' : IsPtAd A a (i + 1) hi β' x' p') (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) :
    xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
  have h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
  dsimp only [xiAd]
  rw [dite_eq_left h, hW i hi β β' x x' x x' p p' _ _ hp hp' h.1.choose_spec h.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)]

theorem exists_u1Af_det (k : ℕ) (hk : k ≤ D.R.m) {g : GL (Fin (D.R.N k)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hg : g ∈ UPts (sigD D) (gramN D k hk) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det g := by
  have hU := det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D k hk) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D k hk) g hg
  set x := Matrix.GeneralLinearGroup.det g with hx
  have hx1 : x * conjId (sigD D) x = 1 := hU
  have h2 : (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) * sigR (sigD D) _ (x : _) = 1 := congrArg Units.val hx1
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : _ →+* Matrix (Fin 1) (Fin 1) _).toMonoidHom x, ?_⟩, ?_⟩
  · change cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) = (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    simp only [cT, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1; funext _; rw [mul_comm]; exact h2
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

end Pt

theorem adLawAt_xiAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hPt : PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := GlobalTheory.T.chartPoints_exist_and_classPoints_representatives A dtU a hPin hTie
  have hE := hPt.1
  have hCo : ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c :=
    GlobalTheory.T.couplingCoset_eq_chartPointCoset A dtU a hPin hTie
  have hMu : MuLaw t u μ dtU := GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain A dtU a hPin hTie
  have hm := m_eq t μ
  have hW : ∀ i hi, PtAway A a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_firstCoupledStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.TwV.AwayTop.ptAway_top A dtU a hPin hTie i hi (by omega)
  have hLev : ∀ i hi, LevAt A dtU a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.lastStep_adelicDatum_level_equivariance A dtU a hPin hTie hE hMu i hi (by omega) (hW i hi)
  have hRat : RatLaw A a := GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain A dtU a hPin hTie hE hW
  have hSize : SizeLaw A a := GlobalTheory.T.adelicDatum_invariance_support_kernelChain A dtU a hPin hTie hE
  have hInt : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z) := GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes A dtU a hPin hTie hE
  refine
    { read := ?_
      rat := hRat
      lev := fun i hi => hLev i hi
      away := ?_
      loc := fun i hi β β' x x' => (hSize i hi β β' x x').1
      supp := fun i hi β β' x x' => (hSize i hi β β' x x').2
      int := hInt
      mu_read := fun i hi => (hMu i hi).1
      mu_cls := ?_
      mu_mul := fun i hi => (hMu i hi).2.1
      mu_alg := fun i hi => (hMu i hi).2.2.1
      mu_unr := fun i hi => (hMu i hi).2.2.2.1
      mu_rat := fun i hi => (hMu i hi).2.2.2.2 }
  · intro i hi c c' z
    rw [xiAd_eq_of_isPtAd hW (hPt.2 i _ c) (hPt.2 (i + 1) hi c')]
    rcases lt_trichotomy i t.m2 with h | h | h
    · rw [hTie.chain.2.2.1 i h c c', xiPt, dite_eq_left h]
    · subst h
      rw [hTie.chain.2.2.2.1 c c', xiPt, dite_eq_right (lt_irrefl _), if_pos rfl, hCo c']
    · obtain rfl : i = t.m2 + 1 := by omega
      rw [hTie.chain.2.2.2.2.1.2 c c', xiPt, dite_eq_right (by omega), if_neg (by omega), hCo c]
  · intro i hi β β' x x' x₁ x₁' hx
    funext z
    obtain ⟨p, hp⟩ := hE i _ β x
    obtain ⟨p', hp'⟩ := hE (i + 1) hi β' x'
    obtain ⟨p₁, hp₁⟩ := hE i _ β x₁
    obtain ⟨p₁', hp₁'⟩ := hE (i + 1) hi β' x₁'
    rw [xiAd_eq_of_isPtAd hW hp₁ hp₁', xiAd_eq_of_isPtAd hW hp hp', hW i hi β β' x x' x₁ x₁' p p' p₁ p₁' hp hp' hp₁ hp₁' hx]
  · intro i hi k hk c
    obtain ⟨y, hy⟩ := exists_u1Af_det k hk ((St k hk).y c).2
    rw [← hy, (hMu i hi).1 y, hTie.dt k hk c y hy]

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  first | exact @GlobalTheory.TwV.adLawAt_xiAd | exact GlobalTheory.TwV.adLawAt_xiAd | (intros; apply GlobalTheory.TwV.adLawAt_xiAd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicDatumWithLawsAtJoint

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.exists_adLawAt_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT :=
  by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J
  exact ⟨_, _, GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel J.A J.dtU J.a J.pins J.tie⟩
end
end
