package ISA_Decls_CSR;
// TODO make this `included rather than imported?

typedef enum {
   //SCR_MTCC,
   //SCR_MEPCC,
   //CSR_MTVAL,
   //CSR_MCAUSE,
   //SCR_STCC,
   //SCR_SEPCC,
   //CSR_STVAL,
   //CSR_SCAUSE,
   //SCR_DPCC,

   SCR_MTDC,
   SCR_MSCRATCHC,
   CSR_MSCRATCH,

   SCR_STDC,
   SCR_SSCRATCHC,
   CSR_SSCRATCH,

   CSR_DSCRATCH0,
   CSR_DSCRATCH1
} CSR_SCR_RegName deriving (Eq, Bits, FShow);


endpackage
