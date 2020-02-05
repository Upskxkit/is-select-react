import React, { ReactElement } from "react";
import "./SelectMenu.scss";
import { MultipleMenu } from "../../interface";
declare function SelectMultiple({ cancelHandler, applyHandler, items, open }: MultipleMenu): ReactElement;
declare namespace SelectMultiple {
    var propTypes: object;
}
declare const _default: React.MemoExoticComponent<typeof SelectMultiple>;
export default _default;
