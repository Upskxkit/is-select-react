import shortid from "shortid";
import {Item} from "../interface";

export const isString = (item: any): Boolean => typeof item === "string";
export const isNumber = (item: any): Boolean => typeof item === "number";

export const isSimpleType = (item: any): Boolean => isString(item) || isNumber(item);

export const isCheckedOption = (item: any, value: any, multi: Boolean) => {
  if (!value) return false;

  if (!multi) {
    return Array.isArray(value)
      ? item.value === value[0].value
      : item.value === value.value;
  }

  if (!Array.isArray(value)) return false;

  return value.some(valueItem => valueItem.value === item.value);
};

//TODO change input type for list/value
export const toOptions = (list: any[] | any, value: any[] | any, multi: Boolean): Item[] =>
  list.map((item: any) => isSimpleType(item) ? {
    value: item,
    label: item,
    checked: isCheckedOption({value: item}, value, multi),
    id: shortid.generate()
  } : {
    ...item,
    checked: isCheckedOption(item, value, multi),
  });
