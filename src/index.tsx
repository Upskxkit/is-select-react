import React, {memo, ReactElement, useEffect, useState} from "react";
import PropTypes from "prop-types";
import ClickAwayListener from "@material-ui/core/ClickAwayListener";
import WithPopper from "./components/WithPopper";
import SelectMultiple from "./components/SelectMenu/SelectMultiple";
import SelectSingle from "./components/SelectMenu/SelectSingle";
import SelectButton from "./components/SelectButton/SelectButton";
import "./index.scss";
import {toOptions} from "./helpers";
import {Item, SelectWrapper} from "./interface";

function Select({
                  type = "default",
                  multi = false,
                  placeholder = "Please select",
                  onSelect,
                  className,
                  list,
                  value,
                  defaultValue,
                  request,
                  hasError = false
                }: SelectWrapper
): ReactElement {

  const [itemList, setItemList] = useState<Item[]>([]);
  const [buttonValue, setButtonValue] = useState<null | string>(null);

  const onSelectHandler = (data: Item | Item[]): void => {
    let label = null;

    onSelect(data);

    if (Array.isArray(data)) {
      if (data.length > 0) label = `${data.length} selected`
    } else {
      label = data.label;
    }

    setButtonValue(label);
  };

  useEffect(() => {

    if (request) {
      request().then((list: []) => {
        setItemList(toOptions(list, value || defaultValue, multi))
      });

      return;
    }

    if (!list || !list.length) return;

    setItemList(toOptions(list, value || defaultValue, multi))
  }, [value, defaultValue, list]);

  useEffect(() => {
    let label = null;

    if (!multi) {
      const item = itemList.find(item => item.checked);

      if (item) label = item.label;

    } else {
      const items = itemList.filter(item => item.checked);

      if (items.length > 0) label = `${items.length} selected`
    }

    setButtonValue(label);

  }, [itemList]);

  return (<WithPopper relative
                      children={(props) => (
                        <ClickAwayListener onClickAway={props.handleClose}>
                          <div className={`${className} selectWrapper ${type}`}>
                            <SelectButton
                              hasError={hasError}
                              type={type}
                              value={buttonValue}
                              placeholder={placeholder}
                              opened={props.open}
                              handleClick={props.handleClick("bottom-end")}/>

                            {multi
                              ? <SelectMultiple open={props.open}
                                                items={itemList}
                                                cancelHandler={props.handleClose}
                                                applyHandler={onSelectHandler}/>
                              : <SelectSingle open={props.open}
                                              items={itemList}
                                              cancelHandler={props.handleClose}
                                              applyHandler={onSelectHandler}/>}
                          </div>
                        </ClickAwayListener>)}/>);
}

Select.propTypes = {
  multi: PropTypes.bool,
  hasError: PropTypes.bool,
  type: PropTypes.oneOf(["circular", "default"]),
  placeholder: PropTypes.string,
  iconUrl: PropTypes.string,
  className: PropTypes.string,
  onSelect: PropTypes.func,
  list: PropTypes.array,
  value: PropTypes.any,
  request: PropTypes.func
};

export default memo(Select);

