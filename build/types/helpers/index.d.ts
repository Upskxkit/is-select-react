import { Item } from "../interface";
export declare const isString: (item: any) => Boolean;
export declare const isNumber: (item: any) => Boolean;
export declare const isSimpleType: (item: any) => Boolean;
export declare const isCheckedOption: (item: any, value: any, multi: Boolean) => boolean;
export declare const toOptions: (list: any, value: any, multi: Boolean) => Item[];
