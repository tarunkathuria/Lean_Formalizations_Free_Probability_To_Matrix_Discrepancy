import ExistenceKS.Main
import ExistenceKS.Audit

/-! These checks compare the complete theorem types, before applying any
implicit arguments, to an independently written primitive proposition. -/
audit_ks_endpoint ExistenceKS.exists_signing
audit_ks_manuscript_endpoint ExistenceKS.exists_signing_manuscript

#print axioms ExistenceKS.exists_signing
#print axioms ExistenceKS.exists_signing_manuscript
