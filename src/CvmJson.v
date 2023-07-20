Require Import CvmJson_Admits Example_Phrases_Admits Term_Defs Cvm_Run.

Definition run_cvm_json (j:JsonT) : JsonT := 
let cvmIn := jsonToCvmIn j in 
    match cvmIn with 
    | CVM_IN t ev => 
        let p := Example_Phrases_Admits.default_place in
        let resev := run_cvm_rawEv t p ev in 
        let cvmout := CVM_OUT resev in 
            cvmOutMessageToJson cvmout 
    end.

Definition run_cvm_json_full (t:Term) (ev:RawEv) : RawEv := 
    let cvmin_json := cvmInMessageToJson (CVM_IN t ev) in 
    let cvmout_json := run_cvm_json cvmin_json in 
    match (jsonToCvmOut cvmout_json) with 
    | CVM_OUT ev' => ev'
    end.